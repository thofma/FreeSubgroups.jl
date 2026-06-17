################################################################################
#
#  Algorithms for biproximal elements
#
################################################################################

# Test if element is (semisimple and) biproximal
#
# # strategy:
# - if no two eigenvalues have the same absolute value, we can decide
#   biproximality using computations with approximations (intervals)
# - otherwise, we have to use a symbolic approach (which is still fast)
function is_semisimple_biproximal(g::MatGroupElem)
  return is_semisimple_biproximal(matrix(g))
end

function is_biproximal(g::MatGroupElem)
  return is_biproximal(matrix(g))
end

_is_semisimple(x::QQMatrix) = is_squarefree(minpoly(x))

_is_semisimple(x::ZZMatrix) = is_squarefree(minpoly(QQ.(x)))

_is_semisimple(x::MatElem{<:FieldElem}) = is_squarefree(minpoly((x)))

function Oscar.roots(CC::ComplexField, g::PolyRingElem{<: EmbeddedNumFieldElem})
  Qb = algebraic_closure(QQ)
  r = roots(change_base_ring(Qb, g))
  return CC.(r)
end

function is_biproximal(g::MatElem)
  CC = complex_field()
  d = nrows(g)
  oldprec = precision(Balls)
  prec = 64
  if is_squarefree(characteristic_polynomial(g))
    while true
      if prec > 2^12
        # precision is getting too large, something might be ood
        break
      end
      set_precision!(Balls, prec)
      local r
      try 
        r = roots(CC, minimal_polynomial(g))
      catch e
        if e isa ErrorException && startswith(e.msg, "unable")
          prec *= 2
          continue
        end
        rethrow(e)
      end
      d = length(r)
      rabs = abs.(r)
      # we need to make sure that no two intervals overlap
      #if any(x -> !(x[1] == x[2]) && overlaps(x[1], x[2]), zip(rabs, rabs))
      #  # we cannot distinguish between "not enough precision" and
      #  # "there are two distinct eigenvalues with the same absolute value"
      #  break
      #end
      sort!(r; by = abs, rev = true )
      if ((abs(r[1]) > abs(r[2])) && (abs(r[d-1]) > abs(r[d]))) 
        set_precision!(Balls, oldprec)
        return true
      else
        set_precision!(Balls, oldprec)
        return false
      end
    end
  end
  # have to do it precisely
  rr = reduce(vcat, [[(r, e) for r in roots(algebraic_closure(QQ), h)] for (h, e) in factor_squarefree(characteristic_polynomial(g))])
  d = nrows(g)
  rrabs = (x -> (abs(x[1]), x[2])).(rr)
  sort!(rrabs; rev = true, by = x -> x[1] )
  if (rrabs[1][2] == 1) && (rrabs[1][1] > rrabs[2][1]) && (rrabs[end-1] > rrabs[end]) && (rrabs[end][2] == 1)
    return true
  else
    return false
  end
end

function is_semisimple_biproximal(g::MatElem)
  CC = complex_field()
  d = nrows(g)
  oldprec = precision(Balls)
  prec = 64
  if !_is_semisimple(g)
    return false
  end
  return is_biproximal(g)
end

################################################################################
#
#  Find semisimple biproximal pair
#
################################################################################

function find_semisimple_biproximal_pair(G)
  pp = elem_type(G)[]
  while true 
    g = _random_element(G; radius = 2)
    if is_semisimple_biproximal(g) 
      push!(pp, g)
      if length(pp) == 2 
        return pp
      end
    end
  end
end

function find_biproximal_pair(G)
  pp = elem_type(G)[]
  while true 
    g, _ = _random_element(G; radius = 2)
    if is_biproximal(g) 
      push!(pp, g)
      if length(pp) == 2 
        return pp
      end
    end
  end
end

function find_semisimple_biproximal_pair_in_gln(n::Int)
  pp = QQMatrix[]
  while true 
    g = _random_element_glnZ(n)
    if is_semisimple_biproximal(g) 
      push!(pp, QQ.(g))
      if length(pp) == 2 
        return pp
      end
    end
  end
end

function find_biproximal_pair_in_gln(n::Int)
  pp = QQMatrix[]
  while true 
    g = _random_element_glnZ(n)
    if is_biproximal(g) 
      push!(pp, QQ.(g))
      if length(pp) == 2 
        return pp
      end
    end
  end
end

################################################################################
#
#  Compute delta(x, y) and eigenvalues
#
################################################################################

# The function returns delta and the sorted eigenvalues of x, x^-1, y, y^-1
function delta(x::MatGroupElem, y::MatGroupElem)
  return delta(matrix(x), matrix(y))
end

function delta(x, y)
   # eigenspaces and eigenvalues
   ux, ex, hx = archimedean_eigenspace_data(x)
   uX, eX, hX = archimedean_eigenspace_data(inv(x))
   uy, ey, hy = archimedean_eigenspace_data(y)
   uY, eY, hY = archimedean_eigenspace_data(inv(y))

   dd = []
   push!(dd, dist_vector_normal_vector(ux, hx))
   push!(dd, dist_vector_normal_vector(uy, hy))
   push!(dd, dist_vector_normal_vector(uX, hX))
   push!(dd, dist_vector_normal_vector(uY, hY))

   push!(dd, dist_vector_normal_vector(ux, hy))
   push!(dd, dist_vector_normal_vector(ux, hY))
   push!(dd, dist_vector_normal_vector(uX, hy))
   push!(dd, dist_vector_normal_vector(uX, hY))

   push!(dd, dist_vector_normal_vector(uy, hx))
   push!(dd, dist_vector_normal_vector(uy, hX))
   push!(dd, dist_vector_normal_vector(uY, hx))
   push!(dd, dist_vector_normal_vector(uY, hX))

   delta = reduce(min, dd)

   return delta, ex, eX, ey, eY, x, inv(x), y, inv(y)
end

################################################################################
#
#  Compute E(x, y)
#
################################################################################

# a1 = largest eigenvalue
# alpha1 = ratio
# d = dimension
# z = -4*log(delta)

function alpha1_and_a1(eigs)
  CC = complex_field()
  return abs(CC(eigs[1])/CC(eigs[2])), abs(CC(eigs[1]))
end

function alpha1_and_a2(eigs)
  CC = complex_field()
  return abs(CC(eigs[1])/CC(eigs[2])), abs(CC(eigs[2]))
end

function Ebound(d, delta, onorm, lambdas::Vector)
  RR = parent(delta)
  z = -4*log(delta) # 4*log(delta^-1))
  alpha1, a2 = RR.(alpha1_and_a2(lambdas))
  return (2 * (d - 2) * log(max(RR(1), inv(sqrt(alpha1) - 1) * onorm* a2^-1)) - 2 * log(delta^2/2))/log(alpha1)
end

#function Ebound(d, delta, lambdas::Vector)
#  RR = parent(delta)
#  z = -4*log(delta) # 4*log(delta^-1))
#  alpha1, a1 = RR.(alpha1_and_a1(lambdas))
#  v = (alpha1-sqrt(alpha1))^-2
#  u = a1^(1 + 1//(d-1))
#  num = (d-2)*log(1+u*v) + z
#  den = abs(log(alpha1))
#  return 2*num/den
#end

function can_compute_biproximal_bound(x, y; check::Bool = true)
  if check
    if !is_biproximal(x) || !is_biproximal(y)
      error("elements must be biproximal")
    end
  end
  RR = real_field()

  d = nrows(x)

  oldprec = precision(Balls)
  # compute delta with "high precision"
  # if not positive, we bail out
  set_precision!(Balls, 1064)
  del, ex, eX, ey, eY = delta(x, y)
  #@info del
  if !is_positive(del)
    set_precision!(Balls, oldprec)
    return false, -1
  end

  oldprec = precision(Balls)
  prec = 64
  while true
    if prec > 2^10
      @error "something off"
      return false, -1
    end
    prec = 2 * prec
    set_precision!(Balls, prec)
    del, ex, eX, ey, eY, x, X, y, Y = delta(x, y)
    #z = -4*log(del) # 4*log(delta^-1))
    #println("compute bounds")
    pp = []
    for (e, a) in [(ex, x), (eX, X), (ey, y), (eY, Y)]
      #@info eX
      _onorm = onorm(a)
      push!(pp, Ebound(d, del, _onorm, e))
    end
    pp = reduce(max, pp)
    fl, cc = unique_integer(ceil(pp))
    if fl
      set_precision!(Balls, oldprec)
      return true, cc
    end
  end
end

bound_biproximal(x, y) = bound_biproximal(matrix(x), matrix(y))

function bound_biproximal(x::MatElem, y::MatElem)
  fl, l = can_compute_biproximal_bound(x, y)
  if !fl
    error("Could not verify that delta(x, y) is positive")
  end
  return l
end

"""
    find_free_pair_biproximal(G::MatrixGroup)

Given a not solvable-by-finite matrix group, return `(x, y), (wx, wy), l`,
where `x` and `y` are elements of `G`, such that `<x^l, y^l>` is a non-abelian
free subgroup of `G`. The elements `wx, wy` are words expressing `x` and `y` in
the generators of `G`.
"""
function find_free_pair_biproximal(G::MatrixGroup; stab = degree(G) > 10 ? 1 : 5, startrad = 5)
  stabbound = stab
  _stab = 0
  k = 0
  currad = startrad
  best_E = typemax(Int)
  best_EE = 0
  best_pair = (one(G), one(G))
  knownpairs = Set{Tuple{elem_type(G), elem_type(G)}}()
  best_word = nothing
  @vprintln :FreeSubgroups 1 "biproximal: looking for random biproximal elements of radius $(currad)"
  while true
    if _stab >= stabbound
      return best_pair, best_word, best_EE
    end
    k += 1
    if k >= 100
      currad += 1
      @vprintln :FreeSubgroups 1 "biproximal: increasing radius to $(currad)"
      k = 0
    end
    x, wx = _random_element(G; radius = currad)
    rx = length(wx)
    y, wy = _random_element(G; radius = currad)
    ry = length(wy)
    if (x, y) in knownpairs
      continue
    end
    push!(knownpairs, (x, y))
    if !is_biproximal(x) || !is_biproximal(y)
      #k = k - 1
      continue
    end
    fl, E = can_compute_biproximal_bound(x, y)
    if !fl
      continue
    end
    if fl && E * max(rx, ry) < best_E
      best_pair = x, y
      best_E = E * max(rx, ry)
      @vprintln :FreeSubgroups 1 "biproximal: found a better pair, new best total bound: $(best_E)"
      best_EE = E
      best_word = (wx, wy)
      #@info best_E, max(estimate_bound(x) * rx, estimate_bound(y) * ry)
      _stab = 0
    else
      _stab += 1
    end
  end
end

function find_free_pair_biproximal(G::MatrixGroup{AbsSimpleNumFieldElem})
  # just embed into GL_n(R) in any form
  k = base_ring(G)
  e = real_embeddings(k)
  E, = Hecke.embedded_field(k, e[1])
  GE = matrix_group(E, degree(G), [E.(matrix(g)) for g in gens(G)])
  (x, y), (wx, wy), l = find_free_pair_biproximal(GE)
  return ((G(map_entries(z -> z.element, matrix(x)); check = false), G(map_entries(z -> z.element, matrix(y)); check = false)),
          (wx, wy),
          l)
end

function find_free_pair_biproximal(G::MatrixGroup{QQBarFieldElem})
  k, ktoQQbar = number_field(QQ, reduce(vcat, [Hecke._eltseq(matrix(g)) for g in gens(G)]))
  Gk = matrix_group(k, degree(G), [preimage.(ktoQQbar, matrix(g)) for g in gens(G)])
  (x, y), (wx, wy), l = find_free_pair_biproximal(Gk)
  return ((G(ktoQQbar.(matrix(x)); check = false), G(ktoQQbar.(matrix(y)); check = false)),
          (wx, wy),
          l)
end
