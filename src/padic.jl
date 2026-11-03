using Oscar
using Oscar: Nemo

struct LowPrecision <: Exception end

function _check_padic_prime(p)
  if !(p isa Union{Integer, ZZRingElem}) || !is_prime(ZZ(p))
    throw(ArgumentError("p must be a prime integer"))
  end
end

abs_val(x) = is_zero(x) ? zero(QQ) : QQ(prime(parent(x)))^(-valuation(x))
abs_val(x, p) = is_zero(x) ? zero(QQ) : QQ(p)^(-valuation(x, p))

_norm_vector(v, p) = maximum(abs_val(x, p) for x in v)
_norm_matrix(m, p) = maximum(_norm_vector(v, p) for v in eachrow(m))

# a zero approximation has valuation equal to its absolute precision
# need a nonzero entry attaining the minimum
function _padic_maximum_abs(entries)
  v = minimum(valuation, entries)
  any(x -> !is_zero(x) && valuation(x) == v, entries) || throw(LowPrecision())
  return QQ(prime(parent(first(entries))))^(-v)
end

function _padic_unit_rows(A)
  B = copy(A)
  for i in 1:nrows(A)
    c = base_ring(A)(_padic_maximum_abs([A[i, j] for j in 1:ncols(A)]))
    for j in 1:ncols(A)
      a = A[i, j]
      if is_zero(a)
        # shift the absolute precision of zero by the exact power of p
        B[i, j] = base_ring(A)(; precision = precision(a) + valuation(c))
      else
        B[i, j] = c * a
      end
    end
  end
  return B
end

# valuation of the ideal of maximal minors = sum of Smith valuations
# need the largest Smith valuation < N
function _padic_maximal_minor_abs(A::MatElem{PadicFieldElem})
  nrows(A) == 0 && return one(QQ)
  N = minimum(precision, A)
  N > 0 || throw(LowPrecision())
  M = map_entries(x -> lift(ZZ, setprecision(x, N)), A)
  ds = Hecke.elementary_divisors(M)
  length(ds) == nrows(A) && !any(is_zero, ds) || throw(LowPrecision())
  p = prime(base_ring(A))
  vals = [valuation(d, p) for d in ds]
  maximum(vals) < N || throw(LowPrecision())
  return QQ(p)^(-sum(vals))
end

# normalize the rows before computing the minor norms
function distance_of_spaces(A, B)
  @assert nrows(A) + nrows(B) == ncols(A)
  A, B = _padic_unit_rows(A), _padic_unit_rows(B)
  a = _padic_maximal_minor_abs(A)
  b = _padic_maximal_minor_abs(B)
  d = det(vcat(A, B))
  is_zero(d) && throw(LowPrecision())
  return abs_val(d)/(a * b)
end

# root valuations in increasing order
function _root_valuations(f, p)
  res = QQFieldElem[]
  for (v, m) in Oscar.GaloisGrp.valuation_of_roots(f, p)
    append!(res, fill(QQ(v), m))
  end
  return sort!(res)
end

function _identify_gaps(s::Vector)
  d = length(s)
  for i in 1:div(d, 2)
    if s[i] > s[i + 1] && s[d - i] > s[d - i + 1]
      return true, i
    end
  end
  return false, 0
end

function _is_good_polynomial(f, p)
  # repeated eigenvalues are allowed
  if is_zero(constant_coefficient(f))
    return false, QQFieldElem[]
  end
  vals = _root_valuations(f, p)
  fl, = _identify_gaps(-vals)
  return fl, vals
end

_is_good_element(mat, p) = _is_good_polynomial(charpoly(matrix(mat)), p)

function _padic_matrix_evaluate(f, X)
  Y = zero(X)
  I = one(parent(X))
  for i in degree(f):-1:0
    Y = Y * X + coeff(f, i) * I
  end
  return Y
end

function _padic_polynomial_kernel(f, X, d)
  Y = _padic_matrix_evaluate(f, X)
  U = kernel(Y; side = :left)
  if nrows(U) != d || !is_zero(U * Y)
    throw(LowPrecision())
  end
  return U
end

# roots of a fixed valuation give a Galois-invariant factor over Q_p
# use its kernel for the generalized eigenspace
function _padic_slope_spaces(x, p; prec = 100)
  f = charpoly(matrix(x))
  fl, vals = _is_good_polynomial(f, p)
  fl || throw(ArgumentError("x must be invertible and have symmetric p-adic gaps"))
  _, i0 = _identify_gaps(-vals)
  d = degree(f)
  Qp = padic_field(p; precision = prec, cached = false)
  R, = polynomial_ring(Qp, :t)
  # convert the coefficients separately
  fp = R([Qp(coeff(f, i)) for i in 0:d])
  fac = Tuple{typeof(fp), Int}[]
  try
    # get multiplicities over Q and keep the full powers
    for (h, m) in factor_squarefree(f)
      hp = R([Qp(coeff(h, i)) for i in 0:degree(h)])
      for (g, m1) in Hecke.slope_factorization(hp)
        push!(fac, (g, m * m1))
      end
    end
  catch e
    # Hecke can lose degree, integrality or residue factors at low precision.
    # 0.41 uses ArgumentErrors; older versions have the other cases below.
    if e isa DivideError || e isa AssertionError ||
       (e isa ArgumentError &&
        (e.msg in ("Insufficient precision for Hensel factorization",
                   "Insufficient precision for slope factorization",
                   "Insufficient precision to determine Newton polygon",
                   "Insufficient precision for polynomial gcd") ||
         startswith(e.msg, "Insufficient precision for exact polynomial division:\n"))) ||
       (e isa ErrorException &&
        (e.msg in ("elt non integral", "Lower convex hull of 1 point is not defined") ||
         startswith(e.msg, "division was not exact:\n"))) ||
       (e isa DomainError && e.val isa Integer && e.val < 0 &&
        e.msg == "Exponent must be non-negative") ||
       (e isa BoundsError && e.a isa Vector{<:PolyRingElem} && isempty(e.a) && e.i == (1,))
      throw(LowPrecision())
    end
    rethrow(e)
  end
  res = Tuple{QQFieldElem, typeof(fp)}[]
  w = QQFieldElem[]
  for (g, m) in fac
    if degree(g) < 1 || is_zero(leading_coefficient(g)) || is_zero(constant_coefficient(g))
      throw(LowPrecision())
    end
    # polynomial powering can also run out of precision
    g = try
      divexact(g, leading_coefficient(g))^m
    catch e
      e isa DivideError && throw(LowPrecision())
      rethrow(e)
    end
    v = QQ(valuation(constant_coefficient(g))) // degree(g)
    # check the Newton slope, including zero approximations
    if !all(i -> valuation(coeff(g, i)) >= (degree(g) - i) * v, 0:degree(g))
      throw(LowPrecision())
    end
    push!(res, (v, g))
    append!(w, fill(v, degree(g)))
  end
  if sort!(w) != vals || prod(g for (_, g) in res) != fp
    throw(LowPrecision())
  end
  fA = prod(g for (v, g) in res if v <= vals[i0])
  fR = prod(g for (v, g) in res if v > vals[i0])
  fAi = prod(g for (v, g) in res if v >= vals[d - i0 + 1])
  fRi = prod(g for (v, g) in res if v < vals[d - i0 + 1])
  X = change_base_ring(Qp, matrix(x))
  V = try
    (_padic_polynomial_kernel(fA, X, i0),
     _padic_polynomial_kernel(fR, X, d - i0),
     _padic_polynomial_kernel(fAi, X, i0),
     _padic_polynomial_kernel(fRi, X, d - i0))
  catch e
    e isa DivideError && throw(LowPrecision())
    rethrow(e)
  end
  return Qp, V, vals, i0
end

function compute_delta(x, b, p; prec)
  Qp, (Ax, Rx, Axi, Rxi), vals, i0 = _padic_slope_spaces(x, p; prec)
  B = change_base_ring(Qp, matrix(b))
  As = (Ax, Axi, Ax * B, Axi * B)
  Rs = (Rx, Rxi, Rx * B, Rxi * B)
  deltas = ntuple(i -> distance_of_spaces(As[i], Rs[i]), 4)
  # four self-distances and eight cross-distances
  delta = minimum(distance_of_spaces(As[i], Rs[j]) for i in 1:4 for j in 1:4
                  if i == j || div(i - 1, 2) != div(j - 1, 2))
  return (field = Qp, delta = delta, self_distances = deltas, valuations = vals, i0 = i0)
end

# Theorem 6.4; alpha_i = p^(v_{i+1}-v_i)
# work with rational exponents
function L_value(x, b, p; prec = 100, maxprec = 1024)
  _check_padic_prime(p)
  prec > 0 && maxprec > 0 || throw(ArgumentError("prec and maxprec must be positive"))
  fl, = _is_good_element(x, p)
  fl || return false, -1
  d = nrows(x)
  while prec <= maxprec
    try
      data = compute_delta(x, b, p; prec)
      vals, i0 = data.valuations, data.i0
      gap = vals[i0 + 1] - vals[i0]
      gapi = vals[d - i0 + 1] - vals[d - i0]
      y = inv(b) * x * b
      Nx = (_norm_matrix(matrix(x), p) * _norm_matrix(matrix(inv(x)), p))^(d - 2)
      Ny = (_norm_matrix(matrix(y), p) * _norm_matrix(matrix(inv(y)), p))^(d - 2)
      # valuation gives log_p for the quotient, which is a power of p
      bounds = [valuation(N // (data.delta * da)^2, p) // g
                for (N, da, g) in zip((Nx, Nx, Ny, Ny), data.self_distances,
                                      (gap, gapi, gap, gapi))]
      return true, max(1, Int(floor(maximum(bounds))) + 1)
    catch e
      e isa LowPrecision || rethrow(e)
      prec *= 2
    end
  end
  return false, -1
end

can_compute_bound_conjugator_padic(x, b, p; kwargs...) = L_value(x, b, p; kwargs...)

function bound_conjugator_padic(x, b, p; kwargs...)
  fl, l = can_compute_bound_conjugator_padic(x, b, p; kwargs...)
  fl || error("Could not verify that bound exists")
  return l
end

# outside the denominator primes of g_i and g_i^-1 the group is bounded
# start with trial division, factor completely for the fallback
function _padic_candidate_primes(matrices, inverses; small_only = false)
  den = one(ZZ)
  for A in Iterators.flatten((matrices, inverses))
    den = lcm(den, denominator(A))
  end
  if small_only
    res, = Nemo.factor_trial_range(den, 0, 1000)
    return sort!(collect(keys(res)))
  end
  return sort!(prime_divisors(den))
end

function _find_random_padic_witness(G, primes; random_samples, radius, source)
  isempty(primes) && return nothing
  for _ in 1:random_samples
    x, word = _random_element(G; radius)
    den = denominator(trace(x))
    for q in primes
      if is_zero(mod(den, q))
        return (prime = q, element = x, word = word, source = source)
      end
    end
  end
  return nothing
end

# all roots are units iff the monic polynomial is integral with unit constant term
function _nonunit_padic_root_prime(f, primes)
  den = denominator(f)
  c = numerator(constant_coefficient(f))
  for p in primes
    if is_zero(mod(den, p)) || is_zero(mod(c, p))
      return p
    end
  end
  return nothing
end

# depth-first search through reduced words of length <= max_length
# prefixes store the corresponding matrices
function _visit_reduced_matrix_words(visit, matrices, inverses, max_length)
  r = length(matrices)
  (r == 0 || max_length == 0) && return nothing
  letters = vcat(matrices, inverses)
  path = Int[]
  prefixes = [one(parent(first(matrices)))]
  next_letter = [1]
  while !isempty(next_letter)
    j = next_letter[end]
    if j > 2*r
      pop!(next_letter)
      if !isempty(path)
        pop!(path)
        pop!(prefixes)
      end
      continue
    end
    next_letter[end] += 1
    if !isempty(path)
      inverse_last = path[end] <= r ? path[end] + r : path[end] - r
      j == inverse_last && continue
    end
    X = prefixes[end] * letters[j]
    push!(path, j)
    result = visit(X, path)
    result === nothing || return result
    if length(path) < max_length
      push!(prefixes, X)
      push!(next_letter, 1)
    else
      pop!(path)
    end
  end
  return nothing
end

# try random trace witnesses, then exhaust words through length d^2
function _find_unbounded_padic_prime(G; p = nothing, random_samples = 100, radius = 5)
  p === nothing || _check_padic_prime(p)
  random_samples >= 0 || throw(ArgumentError("random_samples must be nonnegative"))
  radius > 0 || throw(ArgumentError("radius must be positive"))
  matrices = [matrix(g) for g in gens(G)]
  inverses = inv.(matrices)
  if p === nothing && random_samples > 0
    small_primes = _padic_candidate_primes(matrices, inverses; small_only = true)
    witness = _find_random_padic_witness(G, small_primes; random_samples, radius,
                                       source = :small_prime)
    witness === nothing || return witness
  end
  primes = p === nothing ? _padic_candidate_primes(matrices, inverses) : [ZZ(p)]
  (isempty(primes) || isempty(matrices)) && return nothing
  witness = _find_random_padic_witness(G, primes; random_samples, radius, source = :random)
  witness === nothing || return witness

  @vprintln :FreeSubgroups 1 "p-adic conjugator: exhausting words through length $(degree(G)^2)"
  F = free_group(ngens(G))
  fg = gens(F)
  word_letters = vcat(fg, inv.(fg))
  # Theorem 6.1 with S = {1,g_i,g_i^-1}, also for p<=d
  return _visit_reduced_matrix_words(matrices, inverses, degree(G)^2) do X, path
    q = _nonunit_padic_root_prime(charpoly(X), primes)
    q === nothing && return nothing
    word = one(F)
    for j in path
      word *= word_letters[j]
    end
    return (prime = q, element = G(X; check = false), word = word, source = :exhaustive)
  end
end

"""
    find_free_pair_conjugator_padic(G::MatrixGroup; p = nothing, ...)

Given a not solvable-by-finite matrix group, return `(x, b), (wx, wb), l`,
where `x` and `y = x^b` are elements of `G`, such that `<x^l, y^l>` is a
non-abelian free subgroup of `G`. The elements `wx, wb` are words expressing
`x` and `b` in the generators of `G`.
With `p = nothing`, prime selection first uses bounded trial division and
up to 100 random trace tests, without full integer factorization.
If no witness is found, fully factor the input denominators and try another
100 random trace tests at all possible primes. With an explicit `p`, try
100 random trace tests only at that prime. Each case falls back to complete
characteristic-polynomial exhaustion through word length `degree(G)^2`.
Raise an error if boundedness is proved at all tested primes.
Keep the selected prime fixed while searching for `x` and `b`.
"""
function find_free_pair_conjugator_padic(G::MatrixGroup; p = nothing, startrad = 5, stab = degree(G) > 10 ? 1 : 5)
  witness = _find_unbounded_padic_prime(G; p, radius = startrad)
  if witness === nothing
    if p === nothing
      error("G is bounded at every finite prime; the p-adic conjugator method does not apply")
    else
      error("G is bounded at p = $(p); the p-adic conjugator method does not apply there")
    end
  end
  p = witness.prime
  @vprintln :FreeSubgroups 1 "p-adic conjugator: selected prime $(p) by $(witness.source) search"
  stabbound = stab
  stab = 0
  k = 0
  currad = startrad
  best_E = typemax(Int)
  bestb = nothing
  best_pair = (one(G), one(G))
  best_word = nothing
  knownpairs = Set{Tuple{elem_type(G), elem_type(G)}}()
  wx = nothing
  wb = nothing
  @vprintln :FreeSubgroups 1 "p-adic conjugator: looking for random biproximal element of radius $(currad)"
  nonewbound = 10 * stabbound
  nonew = 0
  while true
    if nonew > nonewbound && bestb !== nothing
      return best_pair, best_word, bestb
    end

    if stab >= stabbound
      return best_pair, best_word, bestb
    end
    k += 1
    if k >= 100
      currad += 1
      @vprintln :FreeSubgroups 1 "p-adic conjugator: increasing radius to $(currad)"
      k = 0
    end
    x, wx = _random_element(G; radius = currad)
    rx = length(wx)

    fl, = _is_good_element(x, p)
    b, wb = _random_element(G; radius = currad)

    if (x, b) in knownpairs
      nonew += 1
      continue
    end

    push!(knownpairs, (x, b))

    if !fl
      nonew += 1
      continue
    end

    rb = length(wb)
    fl, conb = can_compute_bound_conjugator_padic(x, b, p)
    if !fl
      nonew += 1
      continue
    end
    wb = map_word(wb, gens(parent(wx)))

    E = max(rx, 2*rb + rx) * conb
    if fl && E < best_E
      nonew = 0
      best_pair = x, b
      best_word = wx, wb
      bestb = conb
      best_E = E
      stab = 0
      @vprintln :FreeSubgroups 1 "p-adic conjugator: found a better pair, new best total bound: $(best_E)"
    else
      stab += 1
    end
  end
end

function has_p_with_symmetric_gap_in_eigenvalues(g)
  candidates = prime_divisors(denominator(trace(g)))
  isempty(candidates) && return false, 0
  f = charpoly(matrix(g))
  for p in candidates
    fl, = _is_good_polynomial(f, p)
    fl && return true, p
  end
  return false, 0
end

function find_free_pair_conjugator_padic(G::MatrixGroup{AbsSimpleNumFieldElem})
  k = base_ring(G)
  e = real_embeddings(k)
  E, = Hecke.embedded_field(k, e[1])
  GE = matrix_group(E, degree(G), [E.(matrix(g)) for g in gens(G)])
  (x, b), (wx, wb), l = find_free_pair_conjugator_padic(GE)
  return ((G(map_entries(z -> z.element, matrix(x)); check = false), G(map_entries(z -> z.element, matrix(b)); check = false)),
          (wx, wb),
          l)
end

function find_free_pair_conjugator_padic(G::MatrixGroup{QQBarFieldElem})
  k, ktoQQbar = number_field(QQ, reduce(vcat, [Hecke._eltseq(matrix(g)) for g in gens(G)]))
  Gk = matrix_group(k, degree(G), [preimage.(ktoQQbar, matrix(g)) for g in gens(G)])
  (x, b), (wx, wb), l = find_free_pair_conjugator_padic(Gk)
  return ((G(ktoQQbar.(matrix(x)); check = false), G(ktoQQbar.(matrix(b)); check = false)),
          (wx, wb),
          l)
end

