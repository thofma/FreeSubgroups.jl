# dimension benchmark: m random subgroups of SL(n,Q) for each n
# entries r/s with r in -H:H, s in 1:H; divide the first row by det
# use the same groups for every method, with seed 2026 + 1000*n + i by default
# each run has a worker and a time limit; write CSV results after every run
#
# from the package directory:
#   using Oscar, FreeSubgroups
#   include("test/dimension.jl")
#   results = run_dimension_benchmark(ns = 3:2:11, m = 10, H = 10)

using Distributed, Printf, Random

const METHODS = [:biproximal, :conjugator, :padic, :svd, :cartan]
const METHOD_NAMES = Dict(:biproximal => "bi-proximal", :conjugator => "conjugator",
                          :padic => "\$p\$-adic conjugator", :svd => "SVD",
                          :cartan => "Cartan")

# code for the worker

const WORKER_IMPORTS = :(using Oscar, FreeSubgroups, Random)

const WORKER_CODE = quote
  function _random_sl_matrix(rng, n, H)
    while true
      M = matrix(QQ, n, n, [QQ(rand(rng, -H:H), rand(rng, 1:H)) for _ in 1:n^2])
      d = det(M)
      is_zero(d) && continue
      for j in 1:n
        M[1, j] = M[1, j] // d
      end
      @assert is_one(det(M))
      return M
    end
  end

  function random_benchmark_group(n, H, seed)
    rng = Random.Xoshiro(seed)
    A = _random_sl_matrix(rng, n, H)
    B = _random_sl_matrix(rng, n, H)
    return matrix_group(A, B)
  end

  # seed both Julia and GAP
  function _seed_searches(seed)
    Random.seed!(seed)
    try
      GAP.Globals.Reset(GAP.Globals.GlobalMersenneTwister, seed)
    catch
    end
    return nothing
  end

  function _run_method(method, G)
    method === :biproximal && return find_free_pair_biproximal(G)
    method === :conjugator && return find_free_pair_conjugator(G)
    method === :padic && return find_free_pair_conjugator_padic(G)
    method === :svd && return find_free_pair_svd(G)
    method === :cartan && return find_free_pair_cartan(G)
    error("unknown method $method")
  end

  # check the words and return (x, y, k, l)
  function _extract(method, G, r)
    r === nothing && error("no pair returned")
    if method === :biproximal
      (x, y), (wx, wy), l = r
      map_word(wx, gens(G)) == x || error("word for x does not evaluate to x")
      map_word(wy, gens(G)) == y || error("word for y does not evaluate to y")
      return x, y, max(length(wx), length(wy)), Int(l)
    end
    if method in (:conjugator, :padic)
      (x, b), (wx, wb), l = r
    else
      (x, b), (wx, wb) = r
      l = 1
    end
    map_word(wx, gens(G)) == x || error("word for x does not evaluate to x")
    map_word(wb, gens(G)) == b || error("word for b does not evaluate to b")
    return x, x^b, max(length(wx), length(wx^wb)), Int(l)
  end

  function _cones_confirm(G, x, y)
    for e in 2:2:20
      inc = QQ(1, ZZ(10)^e)
      verify_free_pair_cones(G, x, y, 1; inc = inc) && return e
    end
    return 0
  end

  # keep the last pair for the cones check
  const LAST_PAIR = Ref{Any}(nothing)

  function bench_run(method, n, H, seed)
    LAST_PAIR[] = nothing
    try
      G = random_benchmark_group(n, H, seed)
      _seed_searches(seed)
      local r
      t = @elapsed (r = _run_method(method, G))
      x, y, k, l = _extract(method, G, r)
      LAST_PAIR[] = (G, x, y)
      return (status = :ok, time = t, k = k, l = l, inc_exp = 0, msg = "")
    catch err
      return (status = :error, time = NaN, k = 0, l = 0, inc_exp = 0,
              msg = sprint(showerror, err, catch_backtrace()))
    end
  end

  # cones check with inc = 10^-e; return 0 if it fails
  function confirm_last()
    LAST_PAIR[] === nothing && return 0
    G, x, y = LAST_PAIR[]
    return _cones_confirm(G, x, y)
  end

  # a busy worker cannot answer Future polling, so use a channel
  function run_into(chan, f, args...)
    r = try
      f(args...)
    catch err
      (status = :error, time = NaN, k = 0, l = 0, inc_exp = 0,
       msg = sprint(showerror, err, catch_backtrace()))
    end
    put!(chan, r)
    return nothing
  end

  # warm up on a small group
  function warmup_methods(H)
    G = random_benchmark_group(3, H, 0)
    for method in $(METHODS)
      try
        _run_method(method, G)
      catch
      end
    end
    return nothing
  end
end

# also define the worker functions here for remote calls
eval(WORKER_CODE)

# workers

const WORKER = Ref(0)
const WORKER_PID = Ref(0)

function start_worker(H; warmup = true)
  project = Base.active_project()
  w = only(addprocs(1; exeflags = `--project=$project --startup-file=no`))
  Distributed.remotecall_eval(Main, [w], WORKER_IMPORTS)
  Distributed.remotecall_eval(Main, [w], WORKER_CODE)
  WORKER_PID[] = remotecall_fetch(getpid, w)
  WORKER[] = w
  if warmup
    chan = RemoteChannel(() -> Channel{Any}(1), myid())
    remote_do(Main.run_into, w, chan, Main.warmup_methods, H)
    if _wait_for(chan, w, 600.0) !== :ok
      @warn "warm-up did not finish; restarting the worker without it"
      stop_worker()
      return start_worker(H; warmup = false)
    end
  end
  return w
end

function stop_worker()
  WORKER[] == 0 && return
  try
    run(`kill -9 $(WORKER_PID[])`)
  catch
  end
  try
    rmprocs(WORKER[]; waitfor = 0)
  catch
  end
  WORKER[] = 0
  return
end

# wait for the result, a dead worker or the timeout
function _wait_for(chan, w, timeout)
  st = timedwait(() -> isready(chan) || !(w in procs()), timeout; pollint = 0.2)
  st === :ok || return :timeout
  return isready(chan) ? :ok : :crashed
end

function run_with_timeout(method, n, H, seed, confirm, timeout, confirm_timeout)
  WORKER[] == 0 && start_worker(H)
  w = WORKER[]
  chan = RemoteChannel(() -> Channel{Any}(1), myid())
  remote_do(Main.run_into, w, chan, Main.bench_run, method, n, H, seed)
  st = _wait_for(chan, w, timeout)
  if st !== :ok
    stop_worker()
    return (status = st, time = NaN, k = 0, l = 0, inc_exp = 0, msg = "")
  end
  r = take!(chan)
  (r.status === :ok && confirm && method in (:svd, :cartan)) || return r
  # separate timeout for the cones check
  chan = RemoteChannel(() -> Channel{Any}(1), myid())
  remote_do(Main.run_into, w, chan, Main.confirm_last)
  st = _wait_for(chan, w, confirm_timeout)
  if st !== :ok
    stop_worker()
    return merge(r, (status = :unconfirmed, msg = "cones check: $st"))
  end
  e = take!(chan)
  e isa Integer && e > 0 && return merge(r, (inc_exp = e,))
  return merge(r, (status = :unconfirmed, msg = e isa Integer ? "" : string(e.msg)))
end

# summaries

function _median(v)
  s = sort(v)
  n = length(s)
  return isodd(n) ? s[(n + 1) ÷ 2] : (s[n ÷ 2] + s[n ÷ 2 + 1]) / 2
end

_fmt(x::Integer) = string(x)
_fmt(x::Real) = isinteger(x) ? string(Int(x)) : @sprintf("%.1f", x)

function summarise(records, ns, methods)
  S = Dict{Tuple{Int, Symbol}, Any}()
  for n in ns, method in methods
    rs = [r for r in records if r.n == n && r.method == method && r.status != :skipped]
    ok = [r for r in rs if r.status in (:ok, :unconfirmed)]
    S[(n, method)] = (runs = length(rs), ok = length(ok),
                      failures = length(rs) - length(ok),
                      unconfirmed = count(r -> r.status == :unconfirmed, rs),
                      time = isempty(ok) ? nothing : (_median([r.time for r in ok]),
                                                      minimum(r.time for r in ok),
                                                      maximum(r.time for r in ok)),
                      k = isempty(ok) ? nothing : (_median([r.k for r in ok]),
                                                   minimum(r.k for r in ok),
                                                   maximum(r.k for r in ok)),
                      l = isempty(ok) ? nothing : (_median([r.l for r in ok]),
                                                   minimum(r.l for r in ok),
                                                   maximum(r.l for r in ok)))
  end
  return S
end

function print_summary(S, ns, methods, m, H, timeout)
  println("\nMedian [min, max] over $m random groups in SL(n, Q), H = $H, time limit $(timeout) s")
  for n in ns
    println("n = $n")
    for method in methods
      s = S[(n, method)]
      print(@sprintf("  %-11s ", method))
      if s.time === nothing
        println("no successful runs ($(s.failures) failures)")
        continue
      end
      t, k, l = s.time, s.k, s.l
      print(@sprintf("time %.2f s [%.2f, %.2f]", t[1], t[2], t[3]))
      print("   k $(_fmt(k[1])) [$(k[2]), $(k[3])]")
      print("   l $(_fmt(l[1])) [$(l[2]), $(l[3])]")
      s.failures > 0 && print("   failures: $(s.failures)")
      s.unconfirmed > 0 && print("   not confirmed by cones: $(s.unconfirmed)")
      println()
    end
  end

  # Uncomment this block to export LaTeX rows.
  #=
  println("\nLaTeX rows (median Time & k & l for ", join(methods, ", "), "):")
  for n in ns
    cells = String[]
    for method in methods
      s = S[(n, method)]
      if s.time === nothing
        push!(cells, "-- & -- & --")
      else
        mark = s.failures > 0 ? "\$^{$(s.failures)}\$" : ""
        push!(cells, @sprintf("%.2f\\,s%s & %s & %s", s.time[1], mark, _fmt(s.k[1]), _fmt(s.l[1])))
      end
    end
    println("    $n & ", join(cells, " & "), " \\\\")
  end
  println("(A superscript on a time gives the number of failed runs, which are excluded from the medians.)")
  =#
end

# run the benchmark

"""
    run_dimension_benchmark(; ns = 3:2:11, m = 10, H = 10, seed = 2026,
                            timeout = 600.0, methods = METHODS,
                            confirm_upto = 4, confirm_timeout = 120.0, max_n = Dict{Symbol, Int}(),
                            csv = "dimension_results.csv")

For each `n` in `ns`, run each method in `methods` on the same `m` random
groups in SL(n, Q) with entry bound `H`. Runs exceeding `timeout` seconds are
counted as failures. For `n <= confirm_upto`, SVD and Cartan outputs are also
checked with the cones method (l = 1), with a separate time limit
`confirm_timeout`; the search result is kept whether or not the check
succeeds. Since cones works over R, a Cartan
pair that it fails to confirm is still free by Theorem 7.2. A method listed in
`max_n` is skipped for n > max_n[method], e.g. `max_n = Dict(:svd => 5)`.
Raw results are written to `csv`.
Returns the vector of raw records.
"""
function run_dimension_benchmark(; ns = 3:2:11, m = 10, H = 10, seed = 2026,
                                 timeout = 600.0, methods = METHODS,
                                 confirm_upto = 4, confirm_timeout = 120.0, max_n = Dict{Symbol, Int}(),
                                 csv = "dimension_results.csv")
  records = NamedTuple[]
  open(csv, "w") do io
    println(io, "n,i,seed,method,status,time,k,l,cones_inc_exponent,message")
    try
      for n in ns, i in 1:m
        s = seed + 1000 * n + i
        for method in methods
          r = if n > get(max_n, method, typemax(Int))
            (status = :skipped, time = NaN, k = 0, l = 0, inc_exp = 0, msg = "")
          else
            run_with_timeout(method, n, H, s, n <= confirm_upto, timeout, confirm_timeout)
          end
          rec = merge((n = n, i = i, seed = s, method = method), r)
          push!(records, rec)
          msg = replace(rec.msg, '"' => '\'', '\n' => ' ')
          println(io, "$n,$i,$s,$method,$(rec.status),$(rec.time),$(rec.k),$(rec.l),$(rec.inc_exp),\"$msg\"")
          flush(io)
          @info "n = $n, group $i, $method: $(rec.status)" * (rec.status in (:ok, :unconfirmed) ?
                @sprintf(" (%.2f s, k = %d, l = %d)", rec.time, rec.k, rec.l) : "")
          if rec.status === :error
            @error "dimension benchmark failed" n group=i seed=s method details=rec.msg
          end
        end
      end
    finally
      stop_worker()
    end
  end
  S = summarise(records, ns, methods)
  print_summary(S, ns, methods, m, H, timeout)
  println("\nRaw results written to $(abspath(csv))")
  return records
end
