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
      return false, x, 0
    end

    b, rb = _random_element(G; radius = currad)

    if !can_compute_biproximal_bound(x, x^b)[1]
      continue
    end

    bc = base_ring(G) isa EmbeddedNumField ? CC.(Qb.(matrix(b))) : CC.(matrix(b))
    bci = base_ring(G) isa EmbeddedNumField ? CC.(Qb.(matrix(inv(b)))) : CC.(matrix(inv(b)))

    if !_is_conjugator(x, b, ux, nUx, uxm, nUxm, bc, bci)
      continue
    end
 
    return true, b, rb
  end
  return false, x, 0
end

function bound_conjugator(x::MatElem, b::MatElem)
  K = base_ring(x)
  G = GL(nrows(x), K)
  return bound_conjugator(G(x), G(b))
end

function bound_conjugator(x::MatGroupElem, b::MatGroupElem)
  d = nrows(x)
  y = x^b
  del, ex, eX, ey, eY = delta(x, y)
  l = Int(ceil(max(Ebound(d, del, onorm(x), ex), Ebound(d, del, onorm(inv(x)), eX))))
end

"""
    find_free_pair_conjugator(G::MatrixGroup)

Given a not solvable-by-finite matrix group, return `(x, b), (wx, wb), l`,
where `x` and `y = x^b` are elements of `G`, such that `<x^l, y^l>` is a
non-abelian free subgroup of `G`. The elements `wx, wb` are words expressing
`x` and `b` in the generators of `G`.
"""
function find_free_pair_conjugator(G::MatrixGroup; startrad = 5, stab = 5)
  stabbound = stab
  stab = 0
  k = 0
  currad = startrad
  best_E = typemax(Int)
  bestb = nothing
  best_pair = (one(G), one(G))
  knownpairs = Set{Tuple{elem_type(G), elem_type(G)}}()
  wx = nothing
  wb = nothing
  @vprintln :FreeSubgroups 1 "conjugator: looking for random biproximal element of radius $(currad)"
  while true
    if stab >= stabbound
      return best_pair, (wx, wb), bestb
    end
    k += 1
    if k >= 100
      currad += 1
      @vprintln :FreeSubgroups 1 "conjugator: increasing radius to $(currad)"
      k = 0
    end
    x, wx = _random_element(G; radius = currad)
    rx = length(wx)
    if !is_semisimple_biproximal(x)
      continue
    end
    fl, b, wb = _random_conjugator(G, x)
    wb = map_word(wb, gens(parent(wx)))
    if (x, b) in knownpairs
      continue
    end
    push!(knownpairs, (x, b))
    if !fl
      continue
    end
    rb = length(wb)
    conb = bound_conjugator(x, b)
    E = max(rx, 2*rb + rx) * conb
    if fl && E < best_E
      best_pair = x, b
      best_word = wx, wb
      bestb = conb
      best_E = E
      stab = 0
      @vprintln :FreeSubgroups 1 "conjugator: found a better pair, new best total bound: $(best_E)"
    else
      stab += 1
    end
  end
end

function find_free_pair_conjugator(G::MatrixGroup{AbsSimpleNumFieldElem})
  k = base_ring(G)
  e = real_embeddings(k)
  E, = Hecke.embedded_field(k, e[1])
  GE = matrix_group(E, degree(G), [E.(matrix(g)) for g in gens(G)])
  (x, b), (wx, wb), l = find_free_pair_conjugator(GE)
  return ((G(map_entries(z -> z.element, matrix(x)); check = false), G(map_entries(z -> z.element, matrix(b)); check = false)),
          (wx, wb),
          l)
end

function find_free_pair_conjugator(G::MatrixGroup{QQBarFieldElem})
  k, ktoQQbar = number_field(QQ, reduce(vcat, [Hecke._eltseq(matrix(g)) for g in gens(G)]))
  Gk = matrix_group(k, degree(G), [preimage.(ktoQQbar, matrix(g)) for g in gens(G)])
  (x, b), (wx, wb), l = find_free_pair_conjugator(Gk)
  return ((G(ktoQQbar.(matrix(x)); check = false), G(ktoQQbar.(matrix(b)); check = false)),
          (wx, wb),
          l)
end

# julia> k, a = quadratic_field(2)
# (Real quadratic field defined by x^2 - 2, sqrt(2))
# 
# julia> G = matrix_group(k, 3, [k.(Oscar.rand(matrix_space(QQ, 3, 3), -10:10)), k.(Oscar.rand(matrix_space(QQ, 3, 3), -10:10))])
# Matrix group of degree 3
#   over real quadratic field defined by x^2 - 2
# 
# julia> FreeSubgroups.find_free_pair_conjugator(G)
