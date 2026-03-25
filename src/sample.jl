function eigenvalues_abs_float(A::MatElem)
  Ac = ComplexF64.(Matrix{Rational{BigInt}}(A))
  d = nrows(A)
  ev = eigvals(Ac)
  sort!(ev; by = abs, rev = true)
  absev = abs.(ev)
  if isapprox(absev[1], absev[2]) || isapprox(absev[d], absev[d - 1])
    return nothing
  end
  return absev
end

function estimate_bound(A::MatGroupElem)
  return estimate_bound(matrix(A))
end

function estimate_bound(A::MatElem)
  e = eigenvalues_abs_float(A)
  if e === nothing
    return false
  end
  d = length(e)

  a1 = e[1]
  a2 = e[2]
  alpha1 = a1/a2

  R = parent(a1)
  Ry, y = polynomial_ring(R, "log(delta)"; cached = false)
  t = 1/(d-1)
  u = (alpha1^(1/2) - 1)^(-2)
  v = (a2 * a1^t)^2
  w = 2*(d-2)*log(1+u*v) + 4*log(2) - 8*y
  r = log(alpha1)
  bA = w/r

  a1 = e[d]^-1
  a2 = e[d-1]^-1
  alpha1 = a1/a2

  t = 1/(d-1)
  u = (alpha1^(1/2) - 1)^(-2)
  v = (a2 * a1^t)^2
  w = 2*(d-2)*log(1+u*v) + 4*log(2) - 8*y
  r = log(alpha1)
  cA = w/r

  B = ceil(max(constant_coefficient(bA), constant_coefficient(cA))) + 1
  if 0 < B <= typemax(Int)
    return Int(B)
  else
    return nothing
  end
end

function sample_biproximal_element(G::MatrixGroup; radius = 10, stab = 10)
  F = free_group(ngens(G))
  Ggen = gens(G)
  c = 0
  cur_min = typemax(Int)
  cur_elem = one(G)
  local A
  while c < stab
    w = rand_pseudo(F; radius = rank(1:radius))
    A = map_word(w, Ggen)
    b = estimate_bound(A)
    if b === false
      continue
    end
    if b < cur_min
      cur_min = b * length(w)
      c = 1
      cur_elem = A
    end
    c += 1
  end
  return cur_min, A
end
 
# Sample := function(mats, l, k)
#     local F, f, m, c, i, w, A, b, r, a, res;
#     F := FreeGroup(Length(mats));
#     f := GeneratorsOfGroup(F);
#     m := false; 
#     c := 0;
#     while c < l do
#         w := PseudoRandom(F: radius := Random([1..k]));
#         A := MappedWord(w, f, mats);
#         b := Bound(A);
#         if b <> false then
#             r := Length(w);
#             a := List(b, x -> CoefficientsOfUnivariatePolynomial(x)[1]);
#             a := Filtered(a, IsFinite);
#             a := Int(Maximum(a))+1;
#             if m = false or m > r*a then 
#                 m := r*a; 
#                 res := [[r, a, b, A]];
#             elif m = r*a then 
#                 AddSet(res, [r,a,b,A]);
#                 c := c+1;
#             else
#                 c := c+1;
#             fi;
#         fi;
#     od;
# 
#     return res;
# end;
#         
#     
