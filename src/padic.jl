using Oscar
using Oscar: Nemo

struct LowPrecision <: Exception end

abs_val(x) = begin @assert valuation(parent(x)(prime(parent(x)))) == 1; QQ(prime(parent(x)))^(-valuation(x)); end

abs_val(x, p) = QQ(p)^(-valuation(x, p))

#// does sequence contain symmetric gaps?
#
#V3IdentifyGaps := function (s)
#   d := #s;
#   gap := [s[i] - s[i + 1]: i in [1..d div 2]];
#   for i in [1..d div 2] do 
#      one := s[i] - s[i + 1]; 
#      two := s[d - i] - s[d - i + 1]; 
#      if one gt 0 and two gt 0 then 
#          return true, i;
#      end if;
#   end for;
#   // "No gap found";
#   return false, _;
#end function;
#
#// multiplicative valuation 
#V3AbsoluteValue := function (f, p)
#   return p^-Valuation (f);
#end function;
#
function _norm_vector(v, p)
  return maximum([abs_val(x, p) for x in v])
end

#// norm of vector v 
#V3NormVector := function (v, p)
#   return Maximum ([V3AbsoluteValue (v[i], p): i in [1..Degree (v)]]);
#end function;

function _norm_matrix(m, p)
  return maximum([_norm_vector(v, p) for v in eachrow(m)])
end

#V3NormMatrix := function (m, p)
#   vals := [];
#   for i in [1..Nrows (m)] do 
#      vals cat:= [V3NormVector (m[i], p): i in [1..Nrows (m)]];
#   end for;
#   return Maximum (vals);
#end function;
#
#// distance between spaces A and R 
#
function distance_of_spaces(A, B)
  # A, R matrices over Qq
  @assert nrows(A) + nrows(B) == ncols(A)
  ell = nrows(A)

  m = minors(A, ell)
  if !(maximum(valuation.(m)) < precision(base_ring(A)))
    throw(LowPrecision())
  end
  a = maximum(abs_val.(m))

  ell = nrows(B)
  m = minors(B, ell)
  if !(maximum(valuation.(m)) < precision(base_ring(B)))
    throw(LowPrecision())
  end
  b = maximum(abs_val.(m))

  d = det(vcat(A, B))

  if !(valuation(d) < precision(base_ring(B)))
    throw(LowPrecision())
  end

  return abs_val(d)/(a * b)
end

#V3DistanceOfSpaces := function (A, R)
#   assert Dimension (A) + Dimension (R) eq Degree (Generic (A));
#
#   p := Prime (BaseRing (A));
#   B := Basis (A);
#   BA := Matrix (B);
#   ell := #B;
#   minors := Minors (BA, ell);
#   a := Maximum ([V3AbsoluteValue (x, p): x in minors]);
#
#   B := Basis (R);
#   BR := Matrix (B);
#   ell := #B;
#   minors := Minors (BR, ell);
#   r := Maximum ([V3AbsoluteValue (x, p): x in minors]);
#
#   J := VerticalJoin (BA, BR);
#   det := V3AbsoluteValue (Determinant (J), p);
#
#   return det / (a * r);
#end function;
#
#// U contains subspaces of vector spaces defined over various finite 
#// extensions of p-adic field. Embed the spaces in splitting field S 
#
#EmbedInSplittingField := function (S, U) 
#   VS := VectorSpace (S, Degree (Rep (U)));
#   return [sub<VS | [VS!y : y in Basis (u)]>: u in U];
#   // return [sub<VS | [y : y in Basis (u)]>: u in U];
#  // return [sub<VS | [[S!x : x in Eltseq (y)]: y in Basis (u)]>: u in U];
#end function;
#
#// write down A and R spaces 
#V3MyEigenspaces := function (S, m, EV, i0)
#   I := m^0;
#   d := Nrows (m);
#   U := [Nullspace ((m - EV[i] * I)^d): i in [1..i0]];
#   U := EmbedInSplittingField (S, U);
#   U1 := [Nullspace ((m - EV[i] * I)^d): i in [i0 + 1..#EV]];
#   U1 := EmbedInSplittingField (S, U1);
#   return &+U, &+U1;
#end function;
#
#// g is rational matrix; work in Q_p 
#
function _eigenspaces(x, Qq, ev, i0)
  d = nrows(x)
  I = x^0
  Iq = change_base_ring(Qq, matrix(I))
  xq = change_base_ring(Qq, matrix(x))
  U  = reduce(vcat, [kernel((xq - ev[i]*Iq); side = :left) for i in 1:i0])
  U1 = reduce(vcat, [kernel((xq - ev[i]*Iq); side = :left) for i in i0 + 1:d])
  #@info nrows(U)
  #@info nrows(U1)
  @assert nrows(U) + nrows(U1) == d
  return U, U1
end

#V3MyEigenvalues := function (g, p: Precision := 1000)
#   F := pAdicField (p, Precision);
#   d := Nrows (g);
#   MA := MatrixAlgebra (F, d);
#   m := MA!g;
#   cp := CharacteristicPolynomial (m);
#   S := SplittingField (cp);
#   P<x> := PolynomialRing (S);
#   f := P!cp;
#   roots := Roots (f);
#   roots := [x : x in roots];
#   valuation := [AbsoluteValue (Valuation (r[1])): r in roots];
#   ParallelSort (~valuation, ~roots);
#   Reverse (~valuation); Reverse (~roots);
#   return valuation, roots, m, S;
#end function;
#
#// is there a symmetric gap?
#V3IsGoodElement := function (mat, p: Precision := 1000) 
#   val, ev, x := V3MyEigenvalues (mat, p: Precision := Precision);
#   flag, i0 := V3IdentifyGaps (val);
#   return flag, val;
#end function;
#
#// compute delta; input are rational matrices mat and b
#// work in Q_p 

function compute_delta(x, b, p; prec)
  d = nrows(x)
  # while true
  Qq, eigvalsx = _compute_qadic_roots(charpoly(matrix(x)), p; prec)
  @assert issorted(eigvalsx, by = abs_val, rev = true)
  fl, i0 = _identify_gaps(abs_val.(eigvalsx))
  @assert fl
  #@info "" i0
  Ux, Ux1 = _eigenspaces(x, Qq, eigvalsx, i0)
  xm1 = inv(x)
  eigvalsm1 = [inv(e) for e in reverse(eigvalsx)]
  @assert issorted(eigvalsm1, by = abs_val, rev = true)
  Uxm1, Uxm11 = _eigenspaces(xm1, Qq, eigvalsm1, i0)
  #@info "i0", i0
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
  prec = 10
  d = nrows(x)
  while true
    if prec > 2^20
      error("Precision exceeding 2^20, something is off?")
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
      return Int(ceil(valuation(N^(nrows(x) - 2)/(delta * delta_x), p)//valuation(alpha, p)))
    catch e
      if e isa LowPrecision
        prec *= 2
        continue
      end
      rethrow(e)
    end
  end
end

#// first bound from Theorem 16 
function compute_bound(x, b, p)
  l1 = L_value(x, b, p)
  l2 = L_value(x^-1, b, p)
  l3 = L_value(x^b, b, p)
  l4 = L_value((x^-1)^b, b, p)
  return max(l1, l2, l3, l4)
end


#// second bound from Corollary 19 (draft 20 Feb 2026) 
#H_Bound := function (mat, b, p: Precision := 1000)
#   d := Nrows (mat);
#   val, ev, x := V3MyEigenvalues (mat, p: Precision := Precision);
#   flag, i0 := V3IdentifyGaps (val);
#   assert flag;
#
#   EV := [ev[i][1]: i in [1..#ev]];
#   C := BaseRing (Parent (EV[1]));
#   b := Matrix (C, b);
#
#   v := Log (p, V3NormMatrix (x, p));
#   vm1 := Log (p, V3NormMatrix (x^-1, p));
#   vb := Log (p, V3NormMatrix (b^-1 * x * b, p));
#   vbm1 := Log (p, V3NormMatrix (b^-1 * (x^-1) * b, p));
#
#   delta := V3ComputeDelta (mat, b, p: Precision := Precision);
#   F := pAdicField (p, Precision);
#   // fix 
#   v_delta := V3AbsoluteValue (F!delta, p);
#
#   max := Maximum (v + vm1, vb + vbm1); 
#   // fix
#   v_i0 :=  V3AbsoluteValue (EV[i0], p) - V3AbsoluteValue (EV[i0 + 1], p);
#   // fix 
#   v_di0 := V3AbsoluteValue (EV[d - i0], p) - V3AbsoluteValue (EV[d - i0 + 1], p);
#   min := Minimum (v_i0, v_di0);
#   return Ceiling (((d - 2) * max + 4 * v_delta)/  min);
#end function;

#// G \leq GL(d, Q) NOT defined over Z 
#// return [<x, b, b, H>] where <x^ell, (x^b)^ell> is free  for ell >= b or ell >= H
#
function version3(G; min_word_length = 1, max_word_length = 10, number_good = 1, number_random = 100, start_precision = 1000)
  # not defined over Z?

#   "range of length", min_word_length, max_word_length;
  d = degree(G)
  _gens = vcat(gens(G), inv.(gens(G)))
  m = length(_gens)
  Q = free_group(m)
  nmr = 0
  words = [rand_pseudo(Q; radius = max_word_length) for _ in 1:number_random]
  while true
    w = rand(words)
    x = map_word(w, _gens)
    #f = characteristic_polynomial(matrix(mat))
    #if !is_squarefree(f)
    #  continue
    #end
    fl, p = has_p_with_symmetric_gap_in_eigenvalues(x)
    if !fl
      continue
    end

    while true
      b = map_word(rand_pseudo(Q; radius = max_word_length), _gens)
      y = x^b
      bound = compute_bound(x, b, p);
      return x, b, bound
    end
    return mat, p
  end
end

function _root_valuations(f, p)
  #@info f
  r = Oscar.GaloisGrp.valuation_of_roots(f, p)
  #@info r
  res = QQFieldElem[]
  #@info r
  d = lcm([denominator(v) for (v,_) in r])
  for (v, c) in r
    for _ in 1:c
      push!(res, QQ(p)^(ZZ(-1 * d * -v))) # fix the sign
    end
  end
  #res = abs.(res)
  sort!(res; rev = true)
  #@info res
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
    OK = maximal_order(g)
    l = lcm(l, lcm([f for (f, e) in prime_decomposition_type(OK, p)]))
  end

  Qq, = QadicField(Int(p), l, prec)

  rts = elem_type(Qq)[]

  for (g, _) in factor(fminscaled)
    OK = lll(maximal_order(g))
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
    #@info a
    #@info r
    h = parent(g)(inv(basis_matrix([aa^i for i in 0:degree(K) - 1]))[2, :]) 
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


#
#V3MyEigenvalues := function (g, p: Precision := 1000)
#   F := pAdicField (p, Precision);
#   d := Nrows (g);
#   MA := MatrixAlgebra (F, d);
#   m := MA!g;
#   cp := CharacteristicPolynomial (m);
#   S := SplittingField (cp);
#   P<x> := PolynomialRing (S);
#   f := P!cp;
#   roots := Roots (f);
#   roots := [x : x in roots];
#   valuation := [AbsoluteValue (Valuation (r[1])): r in roots];
#   ParallelSort (~valuation, ~roots);
#   Reverse (~valuation); Reverse (~roots);
#   return valuation, roots, m, S;
#end function;

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
      if is_ramified(maximal_order(k), p)
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
  # return true, p if yes
  # return false, 0 if no

#
#   // choose p to define p-adics Q_p 
#   nmr := 0; 
#   words := RandomWords (Q, min_word_length, max_word_length, NumberRandom);
#   repeat 
#      w := Random (words);
#      mat := Evaluate (w, gens);
#      trace := Trace (mat);
#      B := PrimeBasis (Denominator (trace));
#      Exclude (~B, 2);
#      if #B ne 0 then p := Random (B); else p := 2; end if;
#      nmr +:= 1;
#   until p ne 2 or nmr gt NumberRandom * 10;
#   if nmr gt NumberRandom * 10 then error "failed to choose p"; end if;
#
#   "Define p-adic field for p = ", p;
#
#   w := Random (words);
#   b := Evaluate (w, gens);
#
#   Len := [min_word_length .. max_word_length];
#   Good := [];
#   for k in Len do
#      "Process word length k = ", k;
#      words := RandomWords (Q, k, k, NumberRandom);
#      mats := [Evaluate (w, gens): w in words];
#      "Number of words of length ", k , " we consider is ", #mats;
#      for i in [1..#mats] do
#         mat := mats[i];
#         flag, val := V3IsGoodElement (mat, p: Precision := Precision);
#         if flag then 
#            "found good element", val; 
#             bound := V3Bound (mat, b, p: Precision := Precision);
#             "First bound for power of element is ", bound;
#             h_bound := H_Bound (mat, b, p: Precision := Precision);
#             Append (~Good, <mat, b, bound, h_bound>);
#             "H bound for power of element is ", bound;
#             if #Good ge NumberGood then break k; end if;
#         end if;
#      end for;
#   end for;
#   return Good;
#end function;
