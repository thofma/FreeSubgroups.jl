# Reproduce Tables 1 and 2 of "Constructing free subgroups of matrix groups".
#
# Usage (from the package directory):
#   julia> using FreeSubgroups
#   julia> include("test/tables.jl")
#
# Each search is timed in the same call that produces its result.

using Printf

const TVALUES = [17, 101, 1009]
# tau for the cones verification of A^3, B^3 in Table 2 (as in src/bench.jl)
const CONES_INC = Dict(17 => 1//100, 101 => 1//1000, 1009 => 1//5000)

# time f() and return (result, seconds); f is run once before for compilation
function timed(f; warmup = true)
  warmup && f()
  local r
  t = @elapsed (r = f())
  return r, t
end

# word length of the conjugate x^b, used for k in Table 1
conj_len(wx, wb) = length(wx^wb)

# Check word certificates before using their lengths in Table 1.
function check_words(G, x, y, wx, wy)
  @assert map_word(wx, gens(G)) == x "first returned word does not evaluate to its matrix"
  @assert map_word(wy, gens(G)) == y "second returned word does not evaluate to its matrix"
  return nothing
end

# confirm that x and y form a free pair, trying successively thinner cones
function cones_confirm(G, x, y; incs = [QQ(1, ZZ(10)^e) for e in 2:2:20])
  for inc in incs
    verify_free_pair_cones(G, x, y, 1; inc = inc) && return inc
  end
  return nothing
end

function run_tables()
  table1 = Dict{Int, Vector{Any}}()
  table2 = Dict{Int, Vector{Any}}()

  for t in TVALUES
    @info "t = $t"
    A, B, b = burau_representation(t = t)
    G = matrix_group(A, B)

    # ---------------- Table 2: bounds for A, B and verification ----------------
    row2 = []
    l, tt = timed(() -> bound_biproximal(A, B));             push!(row2, (tt, l))
    l, tt = timed(() -> bound_conjugator(A, b));             push!(row2, (tt, l))
    l, tt = timed(() -> bound_conjugator_padic(A, b, t));    push!(row2, (tt, l))
    ok, tt = timed(() -> verify_free_pair_cones(G, A, B, 3; inc = CONES_INC[t]))
    @assert ok "cones verification of A^3, B^3 failed for t = $t"
    push!(row2, (tt, 3))
    table2[t] = row2

    # ---------------- Table 1: searches (randomised; no warm-up rerun) --------
    row1 = []
    # compile once on this group so that timings exclude compilation
    if t == first(TVALUES)
      find_free_pair_biproximal(G); find_free_pair_conjugator(G)
      find_free_pair_conjugator_padic(G); find_free_pair_svd(G); find_free_pair_cartan(G)
    end

    r, tt = timed(() -> find_free_pair_biproximal(G); warmup = false)
    (x, y), (wx, wy), l = r
    check_words(G, x, y, wx, wy)
    push!(row1, (tt, max(length(wx), length(wy)), l))

    r, tt = timed(() -> find_free_pair_conjugator(G); warmup = false)
    (x, bb), (wx, wb), l = r
    check_words(G, x, bb, wx, wb)
    push!(row1, (tt, max(length(wx), conj_len(wx, wb)), l))

    r, tt = timed(() -> find_free_pair_conjugator_padic(G); warmup = false)
    (x, bb), (wx, wb), l = r
    check_words(G, x, bb, wx, wb)
    push!(row1, (tt, max(length(wx), conj_len(wx, wb)), l))

    for (name, f) in [(:svd, find_free_pair_svd), (:cartan, find_free_pair_cartan)]
      r, tt = timed(() -> f(G); warmup = false)
      (x, bb), (wx, wb) = r
      check_words(G, x, bb, wx, wb)
      inc = cones_confirm(G, x, x^bb)
      inc === nothing && error("$name output for t = $t not confirmed by cones")
      @info "$name output for t = $t confirmed by cones with inc = $inc"
      push!(row1, (tt, max(length(wx), conj_len(wx, wb)), 1))
    end
    table1[t] = row1
  end
  return table1, table2
end

table1, table2 = run_tables()

# ---------------- print LaTeX rows ----------------
# Uncomment this block to export LaTeX rows.
#=
println("\nTable 1 rows (Time & k & l for bi-proximal, conjugator, p-adic conjugator, SVD, Cartan):")
for t in TVALUES
  cells = [@sprintf("%.2f\\,s & %d & %d", tt, k, l) for (tt, k, l) in table1[t]]
  println("    $t & ", join(cells, " & "), " \\\\")
end

println("\nTable 2 rows (Time & l for bi-proximal, conjugator, p-adic conjugator, cones):")
for t in TVALUES
  cells = [@sprintf("%.1f\\,ms & %d", 1000 * tt, l) for (tt, l) in table2[t]]
  println("    $t & ", join(cells, " & "), " \\\\")
end
=#
