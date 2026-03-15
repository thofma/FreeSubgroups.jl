# returns true if x is not in the hyperplane with normal vector n
# returns nothing otherwise (answer might be yes or no)
function _is_not_contained_in_hyperplane(x::Vector, n::Vector)
  # n is the normal vector of the hyperplane
  d = dot(x, n)
  if !contains_zero(d)
    return true
  end
  return nothing
end

function is_conjugator(x, b)
  ux, ex, nUx = archimedean_eigenspace_data(matrix(x))
  uxm, exm, nUxm = archimedean_eigenspace_data(inv(matrix(x)))
  CC = complex_field()
  bc = CC.(matrix(b))
  bci = CC.(matrix(inv(b)))
  return _is_conjugator(x, b, ux, nUx, uxm, nUxm, bc, bci)
end

function _is_conjugator(x, b, ux, nUx, uxm, nUxm, bc, bci)
  _is_not_contained_in_hyperplane(ux * bc, nUx) !== true && return false
  _is_not_contained_in_hyperplane(ux * bc, nUxm) !== true && return false
  _is_not_contained_in_hyperplane(uxm * bc, nUx) !== true && return false
  _is_not_contained_in_hyperplane(uxm * bc, nUxm) !== true && return false
  _is_not_contained_in_hyperplane(ux * bci, nUx) !== true && return false
  _is_not_contained_in_hyperplane(ux * bci, nUxm) !== true && return false
  _is_not_contained_in_hyperplane(uxm * bci, nUx) !== true && return false
  _is_not_contained_in_hyperplane(uxm * bci, nUxm) !== true && return false
  return true
end

function _random_conjugator(G, x; prec = 32, maxrad = 10)
  Qb = algebraic_closure(QQ)
  k = 0
  currad = 2
  oldprec = precision(Balls)
  set_precision!(Balls, prec)
  ux, ex, nUx = archimedean_eigenspace_data(matrix(x))
  uxm, exm, nUxm = archimedean_eigenspace_data(inv(matrix(x)))
  CC = complex_field()
  while true
    k += 1
    if k >= 100
      currad += 1
      k = 0
    end

    if currad > maxrad
      return false, x
    end

    b = _random_element(G; radius = currad)

    bc = base_ring(G) isa EmbeddedNumField ? CC.(Qb.(matrix(b))) : CC.(matrix(b))
    bci = base_ring(G) isa EmbeddedNumField ? CC.(Qb.(matrix(inv(b)))) : CC.(matrix(inv(b)))

    if !_is_conjugator(x, b, ux, nUx, uxm, nUxm, bc, bci)
      continue
    end
 
    return true, b
  end
  return false, g
end

function conjugator_bound(x, b)
  d = nrows(x)
  y = x^b
  del, ex, eX, ey, eY = delta(x, y)
  l = Int(ceil(max(Ebound(d, del, ex), Ebound(d, del, eX))))
end

function conjugator_algorithm(G::MatrixGroup)
  stabbound = 10
  stab = 0
  k = 0
  currad = 1
  best_E = typemax(Int)
  best_pair = (one(G), one(G))
  while true
    if stab >= stabbound
      return best_E, best_pair
    end
    k += 1
    if k >= 100
      currad += 1
      k = 0
    end
    x = _random_element(G; radius = currad)
    if !is_semisimple_biproximal(x)
      continue
    end
    fl, b = _random_conjugator(G, x)
    if !fl
      continue
    end
    E = conjugator_bound(x, b)
    if fl && E < best_E
      best_pair = x, b
      best_E = E
      stab = 0
    else
      stab += 1
    end
  end
end

function conjugator_algorithm(G::MatrixGroup{AbsSimpleNumFieldElem})
  k = base_ring(G)
  e = real_embeddings(k)
  E, = Hecke.embedded_field(k, e[1])
  GE = matrix_group(E, degree(G), [E.(matrix(g)) for g in gens(G)])
  return conjugator_algorithm(GE)
end

# 
# julia> k, a = quadratic_field(2)
# (Real quadratic field defined by x^2 - 2, sqrt(2))
# 
# julia> G = matrix_group(k, 3, [k.(Oscar.rand(matrix_space(QQ, 3, 3), -10:10)), k.(Oscar.rand(matrix_space(QQ, 3, 3), -10:10))])
# Matrix group of degree 3
#   over real quadratic field defined by x^2 - 2
# 
# julia> FreeSubgroups.conjugator_algorithm(G)
