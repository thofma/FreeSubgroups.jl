function lower_bound_given_kappa(A, B, kappa)
  del, = delta(A, B)
  res = []
  for a in [A, B, inv(A), inv(B)]
    d = nrows(a)
    a1, a2 = abs.(isolated_biproximal_eigenvalues_sorted_by_absolute_value(a))
    @assert kappa < a1/a2
    del, = delta(A, B)
    bd = lower_bound_from_kappa(a1, a2, d, del)(kappa)
    push!(res, bd)
  end
  return maximum(res)
end

function lower_bound_from_kappa_rigorous(A, B)
  d = nrows(A)
  a1, a2 = abs.(isolated_biproximal_eigenvalues_sorted_by_absolute_value(A))
  del, = delta(A, B)
  return lower_bound_from_kappa(a1, a2, d, del)
end

function lower_bound_from_kappa_fast(A, B)
  a1, a2 = eigenvalues_abs_float(A)
  del = Float64(delta(A, B)[1])
  return lower_bound_from_kappa(a1, a2, d, delta)
end

function lower_bound_from_kappa(a1, a2, d, delta)
  f = kappa -> begin
    D = d - 2
    alpha1 = abs(a1)/abs(a2)
    A = (a2 * a1^(1/(d - 1)))^2
    num = D * log(1 + A/kappa^2) + log(4 * delta^(-4))
    den = log(alpha1/(1 + kappa)); return num/den
  end
  return f
end

function lower_bound(t)
  A, B = burau_representation(;t = t);
  a1, a2, a3 = FreeSubgroups.eigenvalues_abs_float(A);
  @info a1, a2, a3
  @info "compute delta"
  del = FreeSubgroups.delta(A, B)[1] |> Float64
  @info "delta: $del"
  f = n(a1, a2, 3.0, del)
  return optimize(f, 0, 100)
end
