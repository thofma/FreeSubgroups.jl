################################################################################
#
#  SVD method
#
################################################################################

function _eigenvalues(h::MatElem)
  mh = characteristic_polynomial(h)
  res = RealFieldElem[]
  pols = QQPolyRingElem[]
  for (g, e) in factor(mh)
    r = roots(real_field(), mh)
    @assert is_pairwise(!overlaps, r)
    for rr in r
      append!(res, [rr for _ in 1:e])
      append!(pols, [g for _ in 1:e])
    end
  end
  per = sortperm(res; rev = true)
  return res[per], pols[per]
end

function _eigenvalues_of_ggt(g::MatElem)
  h = g * transpose(g)
  return _eigenvalues(h)
end

function _sigmas(g::MatElem; evs = _eigenvalues_of_ggt(g)[1])
  return [sqrt(r) for r in evs]
end

function beta(g::MatElem; evs = _eigenvalues_of_ggt(g)[1])
  _sig = _sigmas(g; evs)
  beta = _sig[1]/_sig[2]
  return beta
end

function rho(g::MatElem; evs = _eigenvalues_of_ggt(g)[1])
  return min(beta(g; evs), beta(inv(g)))
end

operator_norm(g::MatElem; evs = _eigenvalues_of_ggt(g)[1]) = _sigmas(g; evs)[1]

function lipschitz_const(g::MatElem; evs = _eigenvalues_of_ggt(g)[1])
  return (operator_norm(g; evs) * operator_norm(inv(g)))^2
end

function epsilon(g::MatElem; ev = _eigenvalues_of_ggt(g))
  return rho(g)^(-1//2)
end

function _eigenvector_of_largest_eigenvalue(h::MatElem, evs)
  K, a = number_field(evs[2][1]; cached = false)
  Qx = parent(defining_polynomial(K))
  E = eigenspace(h, a)
  v = (x -> (Qx(x))(evs[1][1])).(E[1, :])
  return v
end

function _compute_vgs(g::MatElem)
  ggt = g * transpose(g)
  evggt = _eigenvalues(ggt)
  vg = _eigenvector_of_largest_eigenvalue(ggt, evggt)
  gtg = transpose(g) * g
  evgtg = _eigenvalues(gtg)
  vgt = _eigenvector_of_largest_eigenvalue(gtg, evgtg)
  return vg, vgt
end

_check_z(g, z) = _check_z(matrix(g), matrix(z))

function _check_z(g::MatElem, _z::MatElem)
  vg, vgt = _compute_vgs(g)
  vgm, vgmt = _compute_vgs(inv(g))
  eps = epsilon(g)
  z = map_entries(complex_field(), _z)
  @info "" Float64(dist_vector_normal_vector(vg * z, vgt))
  @info "" 2 * Float64(eps)
  @info Float64(eps)
  if !(dist_vector_normal_vector(vg * z, vgt) >= 2 * eps)
    return false, vg, vg, vg, vg
  end

  @info "" dist_vector_normal_vector(vgm, vgmt * z)
  @info "" 2 * lipschitz_const(_z) * eps

  if !(dist_vector_normal_vector(vgm, vgmt * z) >= 2 * lipschitz_const(_z) * eps)
    return false, vg, vg, vg, vg
  end

  x = g * z
  ax = vg * z
  Bx = vgt
  axbar = vgm
  Bxbar = vgmt * z

  return true, ax, axbar, Bx, Bxbar
end

_check_b(g, z, b, ax, axbar, Bx, Bxbar) = _check_b(matrix(g), matrix(z), matrix(b), ax, axbar, Bx, Bxbar)

function _check_b(g::MatElem, z::MatElem, b::MatElem, ax, axbar, Bx, Bxbar)
  lipb = lipschitz_const(b)
  lipz = lipschitz_const(z)
  eps = epsilon(g)
  @info "" 2 * lipb^2 * lipz * eps
  (dist_vector_normal_vector(ax, Bx) >= 2 * lipb^2 * lipz * eps) || return false
  (dist_vector_normal_vector(axbar, Bxbar) >= 2 * lipb^2 * lipz * eps) || return false
  for u in [ax, axbar]
    for V in [Bx, Bxbar]
      (dist_vector_normal_vector(u * complex_field().(b), V) >= 2 * lipb * lipz * eps) || return false
      (dist_vector_normal_vector(u, V * complex_field().(b)) >= 2 * lipb * lipz * eps) || return false
    end
  end
  return true
end

function svd_algorithm(G::MatrixGroup)
  rad = 2
  k = 0
  while true
    if k >= 200
      @info rad
      rad += 1
      k = 0
    end

    gs = []
    for i in 1:100
      g, rg = _random_element(G; radius = 10*rad)
      #@info g
      push!(gs, (g, rg, epsilon(matrix(g))))
    end
    _, i = findmin(a -> a[3], gs)
    g, rg, eps = gs[i]

    z = rand(gens(G))
    fl, ax, axbar, Bx, Bxbar = _check_z(g, z)
    @warn "_check_z succeed: $fl"
    if !fl
      continue
    end
    b = rand(gens(G))
    fl = _check_b(g, z, b, ax, axbar, Bx, Bxbar)
    if fl
      x = z * g
      return x, b
    end
  end
end
