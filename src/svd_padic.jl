struct PadicSVD
  p::QQFieldElem
  SS::QQMatrix
  U::ZZMatrix
  V::ZZMatrix
  nis::Vector{ZZRingElem}
end

# invariant factors suffice for the singular values
function _padic_singular_valuations(g::QQMatrix, p)
  d = denominator(g)
  ds = Hecke.elementary_divisors(ZZ.(d * g))
  return valuation.(ds, p) .- valuation(d, p)
end

_padic_singular_valuations(g::MatGroupElem, p) = _padic_singular_valuations(matrix(g), p)

sigma(g::QQMatrix, i::Int, p) = QQ(p)^(-_padic_singular_valuations(g, p)[i])

sigma(C::PadicSVD, i::Int) = abs_val(C.p^C.nis[i], ZZ(C.p))

function beta(g, p)
  v = _padic_singular_valuations(g, p)
  return QQ(p)^(v[2] - v[1])
end

beta(C::PadicSVD) = sigma(C, 1)/sigma(C, 2)

function rho(g, p)
  v = _padic_singular_valuations(g, p)
  return QQ(p)^min(v[2] - v[1], v[end] - v[end-1])
end

# sup norm over Q_p
lip(g::QQMatrix, p; ginv = inv(g)) = (_norm_matrix(g, p) * _norm_matrix(ginv, p))^2
lip(g::MatGroupElem, p; ginv = inv(g)) = lip(matrix(g), p; ginv = matrix(ginv))

epsilon(g, p) = (real_field()(rho(g, p)))^(-1//2)

vg(C::PadicSVD) = C.V[1, :]

vgprime(C::PadicSVD) = transpose(C.U)[1, :]

_inv(C::PadicSVD) = PadicSVD(C.p, reverse_cols!(reverse_rows!(inv(C.SS))), reverse_cols!(inv(C.V)), reverse_rows!(inv(C.U)), reverse!((-).(C.nis)))

function Hg(C::PadicSVD)
  vv = vgprime(C)
  K = kernel(matrix(QQ, length(vv), 1, vv), side = :left)
  @assert nrows(K) == length(vv) - 1
  return K
end

function _p_adic_svd(mat::MatGroupElem, p)
  return _p_adic_svd(matrix(mat), p)
end

function _p_adic_svd(mat::QQMatrix, p)
  d = denominator(mat)
  matZZ = ZZ.(d * mat)
  S, U, V = snf_with_transform(matZZ)
  k = valuation(d, p)
  SS = QQ.(S)
  for i in 1:nrows(mat)
    SS[i, i] = SS[i, i]//d
  end
  @assert U * mat * V == SS
  U = inv(U)
  V = inv(V)
  @assert U * SS * V == mat
  return PadicSVD(p, SS, U, V, valuation.(diagonal(SS), p))
end

function _beta_padic(mat::QQMatrix, p; C = _p_adic_svd(mat, p))
  return sigma(C, 1)/sigma(C, 2)
end

function _padic_dist_vector_normal_vector(v, w, p)
  return _padic_dist_vector_vector(v, w, p)
end

function _padic_dist_vector_hypersurface(v, H, p)
  w = kernel(H; side = :right)
  @assert length(w) == length(v)
  return _padic_dist_vector_vector(v, w, p)
end

function _padic_dist_vector_vector(v, w, p)
  return abs_val(dot(v, w), p)/(_norm_vector(v, p) * _norm_vector(w, p))
end

# L*M*R = S; get the first row of R^-1 and column of L^-1 via M
# the inverse uses the last row of L and column of R
# these vectors have p-adic unit norm for every p
function _cartan_directions(M::ZZMatrix)
  S, L, R = snf_with_transform(M)
  v = divexact.(L[1, :] * M, S[1, 1])
  n = divexact.(M * R[:, 1], S[1, 1])
  return QQ.(v), QQ.(n), QQ.(L[end, :]), QQ.(R[:, end])
end

_transform_normal(n::Vector{QQFieldElem}, h::QQMatrix; hinv = inv(h)) = n * transpose(hinv)

# use squared distances to keep everything rational
function _check_cartan_z(z, p, directions, eps2; zinv = inv(z), lipz = lip(z, p; ginv = zinv))
  bound = lipz^2 * eps2
  bound >= 1 && return false, nothing
  v, n, vi, ni = directions
  ax = v * z
  nxinv = _transform_normal(ni, z; hinv = zinv)
  # necessary separation bounds
  _padic_dist_vector_normal_vector(ax, n, p)^2 >= bound || return false, nothing
  _padic_dist_vector_normal_vector(vi, nxinv, p)^2 >= bound || return false, nothing
  return true, (ax, vi, n, nxinv)
end

function _check_cartan_b(b, p, data, eps2, lipz; binv = inv(b))
  ax, axinv, nx, nxinv = data
  @assert _padic_dist_vector_normal_vector(ax, nxinv, p) <= eps2
  bound = (lip(b, p; ginv = binv) * lipz)^2 * eps2
  bound >= 1 && return false
  axb, axinvb = ax * b, axinv * b
  nxb = _transform_normal(nx, b; hinv = binv)
  nxinvb = _transform_normal(nxinv, b; hinv = binv)
  _padic_dist_vector_normal_vector(axb, nxb, p)^2 > bound || return false
  _padic_dist_vector_normal_vector(axinvb, nxinvb, p)^2 > bound || return false
  for (u, ub) in ((ax, axb), (axinv, axinvb))
    for (n, nb) in ((nx, nxb), (nxinv, nxinvb))
      _padic_dist_vector_normal_vector(ub, n, p)^2 > bound || return false
      _padic_dist_vector_normal_vector(u, nb, p)^2 > bound || return false
    end
  end
  return true
end

function is_z_good_for_g(g::MatGroupElem, z::MatGroupElem, p)
  return is_z_good_for_g(matrix(g), matrix(z), p)
end

function is_z_good_for_g(g, z, p)
  directions = _cartan_directions(ZZ.(denominator(g) * g))
  fl, data = _check_cartan_z(z, p, directions, inv(rho(g, p)))
  fl || return false, nothing
  ax, axinv, nx, nxinv = data
  # return bases for the hyperplanes
  Bx = kernel(matrix(QQ, length(nx), 1, nx); side = :left)
  Bxinv = kernel(matrix(QQ, length(nxinv), 1, nxinv); side = :left)
  return true, (ax, axinv, Bx, Bxinv)
end

function is_b_good(b::MatGroupElem, z, ax, axinv, Bx, Bxinv, e, p)
  return is_b_good(matrix(b), matrix(z), ax, axinv, Bx, Bxinv, e, p)
end

function is_b_good(b::QQMatrix, z, ax, axinv, Bx, Bxinv, e, p)
  nx = kernel(Bx; side = :right)[:, 1]
  nxinv = kernel(Bxinv; side = :right)[:, 1]
  return _check_cartan_b(b, p, (ax, axinv, nx, nxinv), e^2, lip(z, p))
end

"""
    find_free_pair_cartan(G::MatrixGroup; stab = degree(G) > 10 ? 1 : 5, startrad = 5)

Find a free pair `(x, x^b)` by the p-adic Cartan method, returning
`(x, b), (wx, wb)`. After a pair is found, stop on stabilization or after
`10 * max(1, stab)` samples of `g` without improvement. Raise `stab` to
spend more time improving the word length.
"""
function find_free_pair_cartan(G::MatrixGroup; stab = degree(G) > 10 ? 1 : 5, startrad = 5)
  stab >= 0 || throw(ArgumentError("stab must be nonnegative"))
  startrad > 0 || throw(ArgumentError("startrad must be positive"))
  rad = startrad
  k = 0
  bestl = typemax(Int)
  bestr = nothing
  _stab = 0
  stabbound = stab
  nonew = 0
  nonewbound = 10 * max(1, stab)
  while true
    if bestr !== nothing && (_stab > stabbound || nonew >= nonewbound)
      return bestr
    end
    bestr === nothing || (nonew += 1)
    k += 1
    if k >= 100
      rad += 1
      k = 0
    end

    g, rg = _random_element(G; radius = 5*rad)
    tg = trace(g)
    lp = Set(vcat(collect(keys(first(Nemo.factor_trial_range(numerator(tg), 0, 1000)))),
                  collect(keys(first(Nemo.factor_trial_range(denominator(tg), 0, 1000))))))
    # compute directions only when needed, then reuse them across primes
    M = ZZ.(denominator(matrix(g)) * matrix(g))
    ds = Hecke.elementary_divisors(M)
    directions = nothing
    for p in lp
      vals = valuation.(ds, p)
      gap = min(vals[2] - vals[1], vals[end] - vals[end-1])
      gap > 0 || continue
      eps2 = QQ(p)^(-gap)
      z, rz = _random_element(G; radius = 1*rad)
      Z = matrix(z)
      Zi = inv(Z)
      lipz = lip(Z, p; ginv = Zi)
      lipz^2 * eps2 < 1 || continue
      if directions === nothing
        directions = _cartan_directions(M)
      end
      fl, data = _check_cartan_z(Z, p, directions, eps2; zinv = Zi, lipz)
      fl || continue
      rz = map_word(rz, gens(parent(rg)))
      x = g * z
      wx = rg * rz
      @assert map_word(wx, gens(G)) == x

      b, rb = _random_element(G; radius = rad)
      _check_cartan_b(matrix(b), p, data, eps2, lipz) || continue
      rb = map_word(rb, gens(parent(rg)))
      lengthpair = max(length(wx), 2*length(rb) + length(wx))
      if lengthpair < bestl
        bestl = lengthpair
        bestr = (x, b), (wx, rb)
        _stab = 0
        nonew = 0
      else
        _stab += 1
      end
    end
  end
end
