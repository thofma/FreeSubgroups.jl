################################################################################
#
#  Ping-pong lemma / cone-based method to verify free subgroups
#
#  Translation of the Magma function VerifyFreeSubgroup by Derek Holt.
#
#  All cone data is stored as rational (QQ) vectors for exactness.
#  The cone membership test uses exact rational arithmetic.
#  Given g1, g2 in GL(d,Q) (or a matrix group over QQ/ZZ), and a power pow,
#  it attempts to verify that <g1^pow, g2^pow> is free of rank 2 by the
#  ping-pong lemma with cones based at the origin.
#
################################################################################

# A cone is represented by its centre (a rational vector, normalised so that
# its norm is slightly > 1), its orthogonal complement vectors OC (rational,
# also normalised), and its generating vectors.
struct PingPongCone
  centre::Vector{QQFieldElem}
  OC::Vector{Vector{QQFieldElem}}  # orthogonal complement directions
  generators::Vector{Vector{QQFieldElem}}
end

# ---------------------------------------------------------------------------
# Auxiliary arithmetic helpers (rational)
# ---------------------------------------------------------------------------

# Squared l2-norm of a rational vector (exact)
function _lv2(v::Vector{QQFieldElem})
  return sum(x^2 for x in v)
end

# A rational lower bound for the l2-norm of v (so that res^2 < lv2(v)).
# Uses ArbField for the sqrt, then converts to QQ via BigFloat with RoundDown,
# and finally corrects rigorously using exact rational arithmetic.
function _lv_lb(v::Vector{QQFieldElem}; precision::Int = 64)
  RR = ArbField(precision)
  lv2 = _lv2(v)
  r = sqrt(RR(lv2))
  # Convert ArbField element to QQ via BigFloat rounded down (guaranteed lower bound)
  bf = BigFloat(r, RoundDown)
  rat = rationalize(BigInt, bf; tol = 0)
  res_rat = QQ(numerator(rat), denominator(rat))
  # Rigorous correction: exact rational check that res_rat^2 < lv2
  d_val = res_rat^2 - lv2
  if d_val > 0
    res_rat -= d_val // res_rat
  end
  return res_rat
end

# Normalise a rational vector: return a rational multiple with length slightly > 1
function _nv(v::Vector{QQFieldElem}; precision::Int = 64)
  lb = _lv_lb(v; precision = precision)
  w = v .// lb
  @assert _lv2(w) >= 1 "normalised vector has squared norm < 1"
  return w
end

# Given a set of vectors S (as rows), return a nonzero vector orthogonal to all of them.
# Uses the right kernel of the matrix with rows S.
function _orthogonal_complement_first(S::Vector{Vector{QQFieldElem}}, d::Int)
  n = length(S)
  A = matrix(QQ, n, d, reduce(vcat, [collect(w) for w in S]))
  # Right kernel of A gives vectors w ∈ QQ^d with A*w = 0, i.e. <row_i, w> = 0
  K = kernel(A; side = :right)
  @assert ncols(K) >= 1
  return QQFieldElem[K[i, 1] for i in 1:d]
end

# Build a rational orthogonal basis for the orthogonal complement of vecs[1].
# Returns d - length(vecs) normalised vectors spanning the orthogonal complement.
function _oc(vecs::Vector{Vector{QQFieldElem}}, d::Int; precision::Int = 64)
  current_span = copy(vecs)
  result = Vector{QQFieldElem}[]
  for _ in (length(vecs) + 1):d
    w = _orthogonal_complement_first(current_span, d)
    wn = _nv(w; precision = precision)
    push!(result, wn)
    push!(current_span, wn)
  end
  return result
end

# ---------------------------------------------------------------------------
# Cone construction
# ---------------------------------------------------------------------------

# Build a cone near the positive ray spanned by vec, with radius inc.
function _vec_cone(vec::Vector{QQFieldElem}, inc::QQFieldElem, d::Int;
           precision::Int = 64)
  v = _nv(vec; precision = precision)
  lo1 = _oc([v], d; precision = precision)
  S = Vector{QQFieldElem}[]
  for w in lo1
    push!(S, v .+ inc .* w)
    push!(S, v .- inc .* w)
  end
  return PingPongCone(v, lo1, S)
end

# ---------------------------------------------------------------------------
# Cone membership test (exact rational arithmetic)
# ---------------------------------------------------------------------------

# Decompose C.centre in the basis [C.OC[1], ..., C.OC[d-1], v]:
#   alpha_1 * OC[1] + ... + alpha_{d-1} * OC[d-1] + lambda * v = C.centre
# If lambda*v is within rad2 of C.centre, v is in the cone.
# Returns (true, sign_of_lambda) if in cone, (false, 0) otherwise.
# All arithmetic is exact rational (no floating point).
function _vec_in_cone(v::Vector{QQFieldElem}, C::PingPongCone, rad2::QQFieldElem)
  d = length(v)
  # M_full: d×d matrix with rows OC[1], ..., OC[d-1], v
  full_rows = vcat([collect(w) for w in C.OC], [collect(v)])
  M_full = matrix(QQ, d, d, reduce(vcat, full_rows))
  centre_mat = matrix(QQ, d, 1, collect(C.centre))
  # Solve (sol as row vector) * M_full = C.centre
  # Equivalently: M_full^T * sol_col = centre_col
  rk, sol_col = can_solve_with_solution(transpose(M_full), centre_mat; side = :right)
  if !rk
    return false, 0
  end
  # sol_col[d] is lambda, the coefficient of v
  lambda = sol_col[d, 1]
  # vn = lambda * v; diff = vn - C.centre = -sum_{i<d} alpha_i * OC[i]
  vn = lambda .* v
  diff = vn .- C.centre
  # Exact rational check: ||diff||^2 < rad2
  if !(_lv2(diff) < rad2)
    return false, 0
  end
  if lambda > 0
    return true, 1
  elseif lambda < 0
    return true, -1
  else
    return false, 0
  end
end

# ---------------------------------------------------------------------------
# Ping-pong check
# ---------------------------------------------------------------------------

# g1mat, g2mat are QQMatrix (already extracted from group elements)
function _check_pingpong(C1, C1i, C2, C2i, g1mat::QQMatrix, g2mat::QQMatrix,
             pow::Int, rad2::QQFieldElem)
  cones = [C1, C1i, C2, C2i]
  # Precompute g^pow and g^{-pow} for g1 and g2
  gens_mat = [g1mat^pow, inv(g1mat)^pow, g2mat^pow, inv(g2mat)^pow]
  # For each cone i, the cones whose images must land in cones[i]:
  # (the "opposite" cone is excluded: C1i for i=1, C1 for i=2, C2i for i=3, C2 for i=4)
  others = [
    [C1, C2, C2i],    # g1^pow  maps C1, C2, C2i  → C1
    [C1i, C2, C2i],   # g1^-pow maps C1i, C2, C2i → C1i
    [C1, C1i, C2],    # g2^pow  maps C1, C1i, C2  → C2
    [C1, C1i, C2i],   # g2^-pow maps C1, C1i, C2i → C2i
  ]
  for i in 1:4
    ci = cones[i]
    g = gens_mat[i]
    for m in others[i]
      # Check that g maps the centre of m into ci
      mc = _apply_matrix(m.centre, g)
      ok, sign = _vec_in_cone(mc, ci, rad2)
      if !ok
        @vprintln :FreeSubgroups 1 "Pingpong conditions fail, i = $i"
        return false
      end
      # Check that g maps every generator of m into ci with the same sign
      for r in m.generators
        rc = _apply_matrix(r, g)
        ok_r, s_r = _vec_in_cone(rc, ci, rad2)
        if !ok_r || s_r != sign
          @vprintln :FreeSubgroups 1 "Pingpong conditions fail (generator check), i = $i"
          return false
        end
      end
    end
  end
  return true
end

# Apply a rational matrix to a rational vector (row vector convention: v*M)
function _apply_matrix(v::Vector{QQFieldElem}, M::QQMatrix)
  return v * M
end

# Check whether mat has an eigenvalue of abs value > 1 and one < 1 (rigorously).
# Uses ball arithmetic (complex_field()) at the given bit precision.
function _is_hyperbolic(mat::QQMatrix; prec::Int = 128)
  CC = complex_field()
  f = characteristic_polynomial(mat)
  oldprec = precision(Balls)
  set_precision!(Balls, prec)
  local rs
  try
    rs = roots(CC, f)
  catch
    set_precision!(Balls, oldprec)
    return false
  end
  set_precision!(Balls, oldprec)
  length(rs) < 2 && return false
  has_exp = any(r -> abs(r) > 1, rs)
  has_con = any(r -> abs(r) < 1, rs)
  return has_exp && has_con
end

# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------

"""
  verify_free_pair_cones(G, g1, g2, pow, inc=0, pow1=50, precision=64) -> Bool

Given a matrix group G over QQ (or ZZ), and elements g1, g2 in G and a
positive integer pow, attempt to verify that <g1^pow, g2^pow> is a free group
of rank 2 using the ping-pong lemma with cones.

Returns `true` if freeness is successfully verified, `false` otherwise.

# Optional keyword arguments
- `inc`: radius parameter for cones (default: 1/100 for d≤4, 1/10000 for d≥5)
- `pow1`: power used to approximate dominant eigenvectors (default: 50)
- `precision`: bit precision used for vector normalisation (default: 64)
"""
function verify_free_pair_cones(G, g1, g2, pow::Int;
                 inc = 0,
                 pow1::Int = 50,
                 precision::Int = 64)
  d = degree(G)
  if inc == 0
    inc = d <= 4 ? QQ(1, 100) : QQ(1, 10000)
  else
    inc = QQ(inc)
  end

  # rad2 = inc^2 / (d-1): squared "radius" threshold for cone membership
  rad2 = inc^2 // (d - 1)

  # Work with rational matrices
  g1mat = QQ.(matrix(g1))
  g2mat = QQ.(matrix(g2))
  g1inv = inv(g1mat)
  g2inv = inv(g2mat)

  # Check g1: needs eigenvalues of abs value both > 1 and < 1
  if !_is_hyperbolic(g1mat; prec = precision * 2)
    @vprintln :FreeSubgroups 1 "The assigned value of g1 does not work"
    return false
  end

  # Approximate dominant/anti-dominant eigenvectors by power iteration
  randm = QQFieldElem[QQ(isodd(i) ? 1 : -1) for i in 1:d]
  v1  = _apply_matrix(randm, g1mat^pow1)
  v1i = _apply_matrix(randm, g1inv^pow1)

  C1  = _vec_cone(v1,  inc, d; precision = precision)
  C1i = _vec_cone(v1i, inc, d; precision = precision)

  # Check g2
  if !_is_hyperbolic(g2mat; prec = precision * 2)
    @vprintln :FreeSubgroups 1 "The assigned value of g2 does not work"
    return false
  end

  v2  = _apply_matrix(randm, g2mat^pow1)
  v2i = _apply_matrix(randm, g2inv^pow1)

  # Check that eigenvectors of g2 are not in cones of g1
  for s in [C1, C1i], v in [v2, v2i]
    ok1, _ = _vec_in_cone(v, s, rad2)
    ok2, _ = _vec_in_cone(.-v, s, rad2)
    if ok1 || ok2
      @vprintln :FreeSubgroups 1 "eigenvector of g2 in a cone of g1"
      return false
    end
  end

  C2  = _vec_cone(v2,  inc, d; precision = precision)
  C2i = _vec_cone(v2i, inc, d; precision = precision)

  # Check that eigenvectors of g1 are not in cones of g2
  for s in [C2, C2i], v in [v1, v1i]
    ok1, _ = _vec_in_cone(v, s, rad2)
    ok2, _ = _vec_in_cone(.-v, s, rad2)
    if ok1 || ok2
      @vprintln :FreeSubgroups 1 "eigenvector of g1 in a cone of g2"
      return false
    end
  end

  if pow != 0
    pingpong = _check_pingpong(C1, C1i, C2, C2i, g1mat, g2mat, pow, rad2)
    if !pingpong
      @vprintln :FreeSubgroups 1 "Assigned g1, g2, pow do not work with these parameters"
      return false
    end
  end

  @vprintln :FreeSubgroups 1 "Freeness successfully verified"
  return true
end
