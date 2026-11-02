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
    r = roots(real_field(), g)
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
  _require_real_archimedean_input(g)
  h = g * transpose(g)
  oldprec = precision(Balls)
  prec = max(64, oldprec)
  try
    while true
      set_precision!(Balls, prec)
      ev = _eigenvalues(h)
      any(is_zero, ev[1]) && throw(ArgumentError("singular matrix"))
      # need ordered, positive eigenvalue intervals
      fl = all(i -> ev[1][i] > ev[1][i+1] || isequal(ev[1][i], ev[1][i+1]),
                    1:length(ev[1])-1)
      if fl && all(is_positive, ev[1]) && all(x -> accuracy_bits(x) >= 32, ev[1])
        return ev
      end
      prec *= 2
    end
  finally
    set_precision!(Balls, oldprec)
  end
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
  # singular values of g^-1 are the reciprocals in reverse order
  return sqrt(min(evs[1]/evs[2], evs[end-1]/evs[end]))
end

operator_norm(g::MatElem; evs = _eigenvalues_of_ggt(g)[1]) = _sigmas(g; evs)[1]

function lipschitz_const(g::MatElem; evs = _eigenvalues_of_ggt(g)[1])
  # squared condition number
  return evs[1]/evs[end]
end

function epsilon(g::MatElem; ev = _eigenvalues_of_ggt(g))
  return rho(g; evs = ev[1])^(-1//2)
end

function _eigenvector_of_largest_eigenvalue(h::MatElem, evs)
  K, a = number_field(evs[2][1]; cached = false)
  Qx = parent(defining_polynomial(K))
  E = eigenspace(h, a)
  v = (x -> (Qx(x))(evs[1][1])).(E[1, :])
  return v
end

function _eigenvector_of_largest_eigenvalue(h::QQMatrix, evs)
  if length(evs[1]) > 1 && isequal(evs[1][1], evs[1][2])
    return invoke(_eigenvector_of_largest_eigenvalue, Tuple{MatElem, Any}, h, evs)
  end
  return _eigenvector_from_isolated_eigenvalue(h, evs[1][1])
end

# row convention, Section 5: v_g comes from g^T*g, v_{g^T} from g*g^T
function _compute_vgs(g::MatElem)
  _require_real_archimedean_input(g)
  gtg = transpose(g) * g
  evgtg = _eigenvalues(gtg)
  vg = _eigenvector_of_largest_eigenvalue(gtg, evgtg)
  ggt = g * transpose(g)
  evggt = _eigenvalues(ggt)
  vgt = _eigenvector_of_largest_eigenvalue(ggt, evggt)
  return vg, vgt
end

function _compute_vgs(g::QQMatrix)
  _require_real_archimedean_input(g)
  h = g * transpose(g)
  ev = _eigenvalues(h)
  vgt = _eigenvector_of_largest_eigenvalue(h, ev)
  # multiplication by g gives the direction for g^T*g
  return vgt * real_field().(g), vgt
end

function _svd_directions(g::MatElem)
  vg, vgt = _compute_vgs(g)
  vgm, vgmt = _compute_vgs(inv(g))
  return vg, vgt, vgm, vgmt
end

# normal of H*h is n*(h^-1)^T
function _transform_normal(n, h::MatElem)
  _require_real_archimedean_input(h)
  return n * complex_field().(transpose(inv(h)))
end

_check_z(g, z; kw...) = _check_z(matrix(g), matrix(z); kw...)

function _check_z(g::MatElem, _z::MatElem; directions = _svd_directions(g), eps = epsilon(g), lipz = lipschitz_const(_z))
  _require_real_archimedean_input(_z)
  vg, vgt, vgm, vgmt = directions
  z = map_entries(complex_field(), _z)
  # (5.3)
  if !(dist_vector_normal_vector(vg * z, vgt) >= 2 * lipz * eps)
    return false, vg, vg, vg, vg
  end

  # (5.4): dist(v_{g^-1}, H_{g^-1} z) >= 2 Lip(z) eps
  Bxbar = _transform_normal(vgmt, _z)
  if !(dist_vector_normal_vector(vgm, Bxbar) >= 2 * lipz * eps)
    return false, vg, vg, vg, vg
  end

  # x = g*z; hyperplanes are represented by their normals
  ax = vg * z
  Bx = vgt
  axbar = vgm

  return true, ax, axbar, Bx, Bxbar
end

_check_b(g, z, b, ax, axbar, Bx, Bxbar; kw...) = _check_b(matrix(g), matrix(z), matrix(b), ax, axbar, Bx, Bxbar; kw...)

function _check_b(g::MatElem, z::MatElem, b::MatElem, ax, axbar, Bx, Bxbar; eps = epsilon(g), lipz = lipschitz_const(z))
  lipb = lipschitz_const(b)
  bc = complex_field().(b)
  # transform the normals once
  Bxb = _transform_normal(Bx, b)
  Bxbarb = _transform_normal(Bxbar, b)
  # (5.5), (5.6): dist(a b, B b) >= 2 Lip(b) Lip(z) eps
  (dist_vector_normal_vector(ax * bc, Bxb) >= 2 * lipb * lipz * eps) || return false
  (dist_vector_normal_vector(axbar * bc, Bxbarb) >= 2 * lipb * lipz * eps) || return false
  # (5.7)
  for u in [ax, axbar]
    for (V, Vb) in ((Bx, Bxb), (Bxbar, Bxbarb))
      (dist_vector_normal_vector(u * bc, V) >= 2 * lipb * lipz * eps) || return false
      (dist_vector_normal_vector(u, Vb) >= 2 * lipb * lipz * eps) || return false
    end
  end
  return true
end

"""
    find_free_pair_svd(G:::MatrixGroup)

Given a not solvable-by-finite matrix group, use the SVD algorithm to find `(x,
b), (wx, wb)`, where `x` and `y = x^b` are a free pair. The elements `wx, wb`
are words expressing `x` and `b` in the generators of `G`.
"""
function find_free_pair_svd(G::MatrixGroup)
  _require_real_archimedean_input(G)
  oldprec = precision(Balls)
  try
    rad = 1
    k = 0
    prec = 64
    set_precision!(Balls, prec)
    while true
      k += 1
      if k >= 10
        rad += 1
        @vprintln :FreeSubgroups 1 "svd method: increasing radius to $(rad)"
        k = 0
      end

      gs = []
      for i in 1:10
        g, rg = _random_element(G; radius = 100*rad)
        #eps = epsilon(matrix(g))
        push!(gs, (g, rg, epsilon(matrix(g))))
      end
      _, i = findmin(a -> a[3], gs)
      g, rg, eps = gs[i]

      # keep the directions for this g
      directions = nothing

      for j in 1:5
        z, rz = _random_element(G; radius = 1*rad)
        local fl, ax, axbar, Bx, Bxbar
        try
          if directions === nothing
            directions = _svd_directions(matrix(g))
          end
          lipz = lipschitz_const(matrix(z))
          fl, ax, axbar, Bx, Bxbar = _check_z(g, z; directions, eps, lipz)
          if !fl
            continue
          end
          b, rb = _random_element(G; radius = 1 * rad)
          fl = _check_b(g, z, b, ax, axbar, Bx, Bxbar; eps, lipz)
          if fl
            x = g * z
            rx = rg * map_word(rz, gens(parent(rg)))
            rb = map_word(rb, gens(parent(rg)))
            return (x, b), (rx, rb)
          end
        catch e
          if e isa LowPrecisionError
            prec = prec * 2
            set_precision!(Balls, prec)
            # recompute at the higher precision
            eps = epsilon(matrix(g))
            directions = nothing
            continue
          end
          rethrow(e)
        end
      end
    end
  finally
    set_precision!(Balls, oldprec)
  end
end
