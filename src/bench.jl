res = Dict()
res2 = Dict()
for t in [17, 101, 1009]
  @info "running benchmark for t = $t"
  times = []
  times2 = []
  A = matrix(QQ, 3, 3, [0, 0, -1//t,  0, -t, -1//t+t,  -1, 0, -1//t+1])
  B = matrix(QQ, 3, 3, [-t, t, 0,     0,  1, 0,          0, 1//t, -1//t])
  b = matrix(QQ, 3, 3, [0, 0, -1, 1, 0, -1, 0, 1, -1])
  G = matrix_group(A, B)

  l = bound_biproximal(A, B)
  tt = @elapsed bound_biproximal(A, B)
  push!(times, (:bound_biproximal, l, tt))

  l = bound_conjugator(A, b)
  tt = @elapsed bound_conjugator(A, b)
  push!(times, (:bound_conjugator, l, tt))


  l = bound_conjugator_padic(A, b, t)
  tt = @elapsed bound_conjugator_padic(A, b, t)
  push!(times, (:bound_conjugator_padic, l, tt))

  if t == 17
    _inc = 1//100
  elseif t == 101
    _inc = 1//1000
  elseif t == 1009
    _inc = 1//5000
  end
  l = verify_free_pair_cones(G, A, B, 3; inc = _inc)
  tt = @elapsed verify_free_pair_cones(G, A, B, 3; inc = _inc)
  push!(times, (:verify_free_pair_cones, l, tt))

  res[t] = times

  # find_free_pair things
  (x, y), (wx, wy), l = find_free_pair_biproximal(G)
  m = max(length(wx), length(wy))
  tt = @elapsed find_free_pair_biproximal(G)
  push!(times2, (:find_free_pair_biproximal, ((x, y), (wx, wy), m, l), tt))

  (x, b), (wx, wb), l = find_free_pair_conjugator(G)
  m = max(length(wx), length(wx^wb))
  tt = @elapsed find_free_pair_conjugator(G)
  push!(times2, (:find_free_pair_conjugator, ((x, b), (wx, wb), m, l), tt))

  (x, b), (wx, wb), l = find_free_pair_conjugator_padic(G)
  m = max(length(wx), length(wx^wb))
  tt = @elapsed find_free_pair_conjugator_padic(G)
  push!(times2, (:find_free_pair_conjugator_padic, ((x, b), (wx, wb), m, l), tt))

  (x, b), (wx, wb) = find_free_pair_svd(G)
  m = max(length(wx), length(wx^wb))
  tt = @elapsed find_free_pair_svd(G)
  push!(times2, (:find_free_pair_svd, ((x, b), (wx, wb), m, 1), tt))

  (x, b), (wx, wb) = find_free_pair_cartan(G)
  m = max(length(wx), length(wx^wb))
  tt = @elapsed find_free_pair_cartan(G)
  push!(times2, (:find_free_pair_cartan, ((x, b), (wx, wb), m, 1), tt))
  res2[t] = times2
  @info "done"
end
