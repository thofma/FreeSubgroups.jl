struct PadicSVD
  p::QQFieldElem
  SS::QQMatrix
  U::ZZMatrix
  V::ZZMatrix
  nis::Vector{ZZRingElem}
end

sigma(g::QQMatrix, i::Int, p) = sigma(_p_adic_svd(g, p), i)

sigma(C::PadicSVD, i::Int) = abs_val(C.p^C.nis[i], ZZ(C.p))

beta(g, p) = beta(_p_adic_svd(g, p))

beta(C::PadicSVD) = sigma(C, 1)/sigma(C, 2)

rho(g, p) = min(beta(g, p), beta(inv(g), p))

lip(g, p) = (sigma(g, 1, p) * sigma(inv(g), 1, p))^2

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

function is_z_good_for_g(g::MatGroupElem, z::MatGroupElem, p)
  return is_z_good_for_g(matrix(g), matrix(z), p)
end

function is_z_good_for_g(g, z, p)
  Cg = _p_adic_svd(g, p)
  _eps = epsilon(g, p)
  _vg = vg(Cg)
  _Hg = Hg(Cg)
  if _padic_dist_vector_hypersurface(_vg * z, _Hg, p) < _eps
    return false, nothing
  end
  #Cginv = _inv(Cg)
  Cginv = _p_adic_svd(inv(g), p)
  _vginv = vg(Cginv)
  _Hginv = Hg(Cginv)
  if _padic_dist_vector_hypersurface(_vginv, _Hginv * z, p) < lip(z, p) * _eps
    return false, nothing
  end
  ax = _vg * z
  Bx = _Hg
  axinv = _vginv
  Bxinv = _Hginv * z
  return true, (ax, axinv, Bx, Bxinv)
end

function is_b_good(b::MatGroupElem, z, ax, axinv, Bx, Bxinv, e, p)
  return is_b_good(matrix(b), matrix(z), ax, axinv, Bx, Bxinv, e, p)
end

function is_b_good(b::QQMatrix, z, ax, axinv, Bx, Bxinv, e, p)
  @assert _padic_dist_vector_hypersurface(ax, Bxinv, p) <= e^2
  lipb = lip(b, p)
  lipz = lip(z, p)
  lb = lipb * lipz * e
  !(_padic_dist_vector_hypersurface(ax * b, Bx * b, p) > lb) && return false
  !(_padic_dist_vector_hypersurface(axinv * b, Bxinv * b, p) > lb) && return false
  for u in [ax, axinv]
    for V in [Bx, Bxinv]
      !(_padic_dist_vector_hypersurface(u * b, V, p) > lb) && return false
      !(_padic_dist_vector_hypersurface(u, V * b, p) > lb) && return false
    end
  end
  return true
end


function find_free_pair_cartan(G::MatrixGroup; stab = 5, startrad = 5)
  rad = startrad
  k = 0
  #while true
  bestl = inf
  bestr = nothing
  _stab = 0
  stabbound = stab
  while true
    if _stab > stabbound
      return bestr
    end
    k += 1
    if k >= 100
      rad += 1
      k = 0
    end

    g, rg = _random_element(G; radius = 5*rad)
    tg = trace(g)
    lp = Set(vcat(collect(keys(first(Nemo.factor_trial_range(numerator(tg), 0, 1000)))),
                  collect(keys(first(Nemo.factor_trial_range(denominator(tg), 0, 1000))))))
    for p in lp
      epsg = epsilon(matrix(g), p)
      if epsg >= 1
        continue
      end
      z, rz = _random_element(G; radius = 1*rad)
      rz = map_word(rz, gens(parent(rg)))
      fl, data = is_z_good_for_g(g, z, p)
      if !fl
        continue
      end
      x = g * z
      wx = rg * rz
      @assert map_word(wx, gens(G)) == x
      ax, axinv, Bx, Bxinv = data

      b, rb = _random_element(G; radius = rad)
      rb = map_word(rb, gens(parent(rg)))
      fl = is_b_good(b, z, ax, axinv, Bx, Bxinv, epsg, p)
      if !fl
        continue
      end
      lengthpair = max(length(wx), 2*length(rb) + length(wx))
      if lengthpair < bestl
        bestl = lengthpair
        bestr = (x, b), (wx, rb)
        _stab = 0
      else
        _stab += 1
      end
    end
  end
end
