using Oscar
using Oscar: Nemo

struct LowPrecision <: Exception end

abs_val(x) = begin @assert valuation(parent(x)(prime(parent(x)))) == 1; QQ(prime(parent(x)))^(-valuation(x)); end

abs_val(x, p) = is_zero(x) ? zero(QQ) : QQ(p)^(-valuation(x, p))

function _norm_vector(v, p)
  return maximum([abs_val(x, p) for x in v])
end

function _norm_matrix(m, p)
  return maximum([_norm_vector(v, p) for v in eachrow(m)])
end

# distance between spaces A and R 
function distance_of_spaces(A, B)
  # A, R matrices over Qq
  @assert nrows(A) + nrows(B) == ncols(A)
  ell = nrows(A)

  m = minors(A, ell)
  if !(minimum(valuation.(m)) < precision(base_ring(A)))
    throw(LowPrecision())
  end
  a = maximum(abs_val.(m))

  ell = nrows(B)
  m = minors(B, ell)
  if !(minimum(valuation.(m)) < precision(base_ring(B)))
    throw(LowPrecision())
  end
  b = maximum(abs_val.(m))

  d = det(vcat(A, B))

  if !(valuation(d) < precision(base_ring(B)))
    throw(LowPrecision())
  end

  return abs_val(d)/(a * b)
end

function _eigenspaces(x, Qq, ev, i0)
  d = nrows(x)
  I = x^0
  Iq = change_base_ring(Qq, matrix(I))
  xq = change_base_ring(Qq, matrix(x))
  U  = reduce(vcat, [kernel((xq - ev[i]*Iq); side = :left) for i in 1:i0])
  U1 = reduce(vcat, [kernel((xq - ev[i]*Iq); side = :left) for i in i0 + 1:d])
  if nrows(U) + nrows(U1) < d
    throw(LowPrecision())
  end
  @assert nrows(U) + nrows(U1) == ncols(U)
  return U, U1
end

function compute_delta(x, b, p; prec)
  d = nrows(x)
  Qq, eigvalsx = _compute_qadic_roots(charpoly(matrix(x)), p; prec)
  @assert issorted(eigvalsx, by = abs_val, rev = true)
  fl, i0 = _identify_gaps(abs_val.(eigvalsx))
  @assert fl
  Ux, Ux1 = _eigenspaces(x, Qq, eigvalsx, i0)
  @assert nrows(Ux) + nrows(Ux1) == d
  xm1 = inv(x)
  eigvalsm1 = [inv(e) for e in reverse(eigvalsx)]
  @assert issorted(eigvalsm1, by = abs_val, rev = true)
  Uxm1, Uxm11 = _eigenspaces(xm1, Qq, eigvalsm1, i0)
  @assert nrows(Uxm1) + nrows(Uxm11) == d
  bb = matrix(b)
  Uxb = Ux * bb
  Ux1b = Ux1 * bb
  Uxm1b = Uxm1 * bb
  Uxm11b = Uxm11 * bb
  delta_x = distance_of_spaces(Ux, Ux1)
  delta = [ 
    delta_x, 
    distance_of_spaces( Ux, Ux1),
    distance_of_spaces( Uxm1, Uxm11),
    distance_of_spaces( Uxb, Ux1b),
    distance_of_spaces( Uxm1b, Uxm11b),

    distance_of_spaces( Uxb, Ux1),
    distance_of_spaces( Ux, Ux1b), 

    distance_of_spaces( Uxb, Uxm11),
    distance_of_spaces( Ux, Uxm11b),
    distance_of_spaces( Uxm1b, Ux1),
    distance_of_spaces( Uxm1, Ux1b),
    distance_of_spaces( Uxm1b, Uxm11),
    distance_of_spaces( Uxm1, Uxm11b)
   ]
  return Qq, minimum(delta), delta_x, eigvalsx
end

function L_value(x, b, p; prec = 10)
  prec = 100
  d = nrows(x)
  while true
    if prec > 2^10
      return false, -1
    end
    try
      Qq, delta, delta_x, eigvalsx = compute_delta(x, b, p; prec)
      N = (_norm_matrix(matrix(x), p) * _norm_matrix(matrix(inv(x)), p))^(d - 2)
      val = abs_val.(eigvalsx)
      fl, i0 = _identify_gaps(val)
      vall = valuation.(eigvalsx)
      @assert fl
      alpha = QQ(p)^-(vall[i0] - vall[i0 + 1])
      @assert alpha == val[i0]/val[i0 + 1]
      return true, Int(ceil(valuation(N^(nrows(x) - 2)/(delta * delta_x), p)//valuation(alpha, p)))
    catch e
      #@info "here"
      #rethrow(e)
      if e isa LowPrecision
        prec *= 2
        continue
      end
      rethrow(e)
    end
  end
end

function can_compute_bound_conjugator_padic(x, b, p)
  fl, l1 = L_value(x, b, p)
  !fl && return false, -1
  fl, l2 = L_value(x^-1, b, p)
  !fl && return false, -1
  fl, l3 = L_value(inv(b)*x*b, b, p)
  !fl && return false, -1
  fl, l4 = L_value(inv(b) * (x^-1)*b, b, p)
  !fl && return false, -1
  return true, max(l1, l2, l3, l4)
end

function bound_conjugator_padic(x, b, p)
  fl, l = can_compute_bound_conjugator_padic(x, b, p)
  if !fl
    error("Could not verify that bound exists")
  end
  return l
end

"""
    find_free_pair_conjugator_padic(G::MatrixGroup)

Given a not solvable-by-finite matrix group, return `(x, b), (wx, wb), l`,
where `x` and `y = x^b` are elements of `G`, such that `<x^l, y^l>` is a
non-abelian free subgroup of `G`. The elements `wx, wb` are words expressing
`x` and `b` in the generators of `G`.
"""
function find_free_pair_conjugator_padic(G::MatrixGroup; startrad = 5, stab = 50)
  stabbound = stab
  stab = 0
  k = 0
  currad = startrad
  best_E = typemax(Int)
  bestb = nothing
  best_pair = (one(G), one(G))
  knownpairs = Set{Tuple{elem_type(G), elem_type(G)}}()
  p = -1
  wx = nothing
  wb = nothing
  @vprintln :FreeSubgroups 1 "p-adic conjugator: looking for random biproximal element of radius $(currad)"
  nonewbound = 10 * stabbound
  nonew = 0
  while true
    if nonew > nonewbound && bestb !== nothing
      return best_pair, (wx, wb), bestb
    end

    if stab >= stabbound
      return best_pair, (wx, wb), bestb
    end
    k += 1
    if k >= 100
      currad += 1
      @vprintln :FreeSubgroups 1 "p-adic conjugator: increasing radius to $(currad)"
      k = 0
    end
    x, wx = _random_element(G; radius = currad)
    rx = length(wx)

    fl, p = has_p_with_symmetric_gap_in_eigenvalues(x)
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

function _root_valuations(f, p)
  r = Oscar.GaloisGrp.valuation_of_roots(f, p)
  res = QQFieldElem[]
  d = lcm([denominator(v) for (v,_) in r])
  for (v, c) in r
    for _ in 1:c
      push!(res, QQ(p)^(ZZ(d * -v))) # fix the sign
    end
  end
  sort!(res; rev = true)
  return res
end

function _identify_gaps(s::Vector)
  d = length(s)
  for i in 1:div(d, 2)
    one = s[i] - s[i + 1]
    two = s[d - i] - s[d - i + 1]
    if one > 0 && two > 0
      return true, i
    end
  end
  return false, 0
end

function _is_good_element(mat, p)
  f = charpoly(matrix(mat))
  if !is_squarefree(f)
    return false, Int[]
  end
  vals = _root_valuations(f, p)
  fl, i0 = _identify_gaps(vals)
  return fl, vals
end

function _compute_qadic_roots(f, p; prec = 100)
  fmin = f
  dd = denominator(fmin)
  fminscaled = fmin(gen(parent(fmin))/dd) * dd^degree(fmin)
  l = 1
  for (g, _) in factor(fminscaled)
    #OK = maximal_order(g)
    OK = pmaximal_overorder(equation_order(g), p)
    l = lcm(l, lcm([f for (f, e) in prime_decomposition_type(OK, p)]))
  end

  Qq, = QadicField(Int(p), l, prec)

  rts = elem_type(Qq)[]

  for (g, _) in factor(fminscaled)
    #OK = lll(maximal_order(g))
    OK = lll(pmaximal_overorder(equation_order(g), p))
    K = Hecke.nf(OK)
    k = 0
    B = Hecke.elem_in_nf.(basis(OK))
    local a
    local r
    while true
      k += 1
      if k > 1000
        error("something off")
      end
      #@info k
      a = OK(rand(B, -10:10), false)
      ma = minpoly(a)
      if mod(discriminant(ma), p) != 0
        #r = roots(Hecke.qAdicRootCtx(ma, Int(p); splitting_field = true), prec)
        r = roots(Qq, ma)
        #@info a
        #@info r
        if length(r) == degree(g)
          #@info minpoly(a).(r)
          break
        end
      end
    end
    aa = elem_in_nf(a)
    # gen(K) expressed as a polynomial in a
    if degree(K) == 1
      h = one(parent(g)) * coeff(gen(K), 0)
    else
      h = parent(g)(inv(basis_matrix([aa^i for i in 0:degree(K) - 1]))[2, :]) 
    end
    @assert h(aa) == gen(K)
    @assert all(is_zero, g.(h.(r)))
    append!(rts, h.(r))
    # need to express 
  end

  rts = Ref(inv(QQ(dd))) .* rts
  @assert all(is_zero, fmin.(rts))
  #@info _root_valuations(fmin, p)

  @assert length(rts) == degree(f)
  sort!(rts, by = valuation)
  return Qq, rts
end

function has_p_with_symmetric_gap_in_eigenvalues(g)
  t = trace(g)
  d = denominator(t)

  fmin = charpoly(matrix(g))
  dd = denominator(fmin)
  fminscaled = fmin(gen(parent(fmin))/dd) * dd^degree(fmin)
  gf = factor(fminscaled)

  for p in prime_divisors(d)
    if p == 2 || p <= nrows(g)
      continue
    end
    fl, = _is_good_element(g, p)
    if !fl
      continue
    end

    #if fl
    #  return true, p
    #end
    # I want an unramified splitting field
    pbad = false
    for (ff, e) in gf
      @assert is_one(e)
      k, = number_field(ff)
      oo = any_order(k)
      oop = pmaximal_overorder(oo, p)
      if mod(discriminant(oop), p) == 0 # is_ramified(maximal_order(k), p)
        pbad = true
        break
      end
    end
    if pbad
      continue
    end
    return true, p
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

