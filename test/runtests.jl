using Test, FreeSubgroups

let
  G = GL(3, QQ)
  A = matrix(QQ, 3, 3, [0, 0, 1//10, 0, -10, 99//10, -1, 0, 9//10])
  B = matrix(QQ, 3, 3, [-10, 10, 0, 0, 1, 0, 0, 1//10, -1//10])
  fl, l = can_compute_biproximal_bound(A, B)
  @test fl
  l = bound_biproximal(A, B)
  A = G(A)
  B = G(B)
  fl, l = can_compute_biproximal_bound(A, B)
  @test fl
  l = bound_biproximal(A, B)
end

let
  A = matrix(QQ, 3, 3, [0, 0, 1//10, 0, -10, 99//10, -1, 0, 9//10])
  B = matrix(QQ, 3, 3, [-10, 10, 0, 0, 1, 0, 0, 1//10, -1//10])
  G = matrix_group([A, B])
  find_free_pair_biproximal(G)
  find_free_pair_conjugator(G)
  find_free_pair_conjugator_padic(G)
  find_free_pair_svd(G)
  find_free_pair_cartan(G)
end

let
  Q, = rationals_as_number_field()
  Qb = algebraic_closure(QQ)
  for k in (Q, Qb)
    A = matrix(k, 3, 3, [0, 0, 1//10, 0, -10, 99//10, -1, 0, 9//10])
    B = matrix(k, 3, 3, [-10, 10, 0, 0, 1, 0, 0, 1//10, -1//10])
    G = matrix_group([A, B])
    find_free_pair_biproximal(G)
    find_free_pair_conjugator(G)
  end
end

let # biproximal
  a = QQ[3 0 0 0;
         0 2 1 0;
         0 0 2 0;
         0 0 0 1]
  @test is_biproximal(a)
  a = QQ[3 0 0 0;
         0 2 1 0;
         0 0 2 0;
         0 0 0 2]
  @test !is_biproximal(a)
  a = QQ[2 0 0 0;
         0 3 1 0;
         0 0 3 0;
         0 0 0 1]
  @test !is_biproximal(a)
  a = QQ[3 0 0 0;
         0 2 1 0;
         0 0 1 0;
         0 0 0 1]
  @test !is_biproximal(a)
end

let # padic bound
  A = matrix(QQ, 3, 3, QQFieldElem[0, 0, -1//11, 0, -11, 120//11, -1, 0, 10//11])
  b = matrix(QQ, 3, 3, [0, 0, -1, 1, 0, -1, 0, 1, -1])
  l = bound_conjugator_padic(A, b, 11)
  @test l == 5
end

include("pingpong.jl")
include("corrections.jl")
include("conjugator_precision.jl")
include("svd.jl")
include("dimension_regression.jl")
include("dim20_regression.jl")
include("archimedean_input.jl")
include("padic.jl")
include("padic_minors.jl")
include("padic_precision.jl")
include("padic_repeated_eigenvalues.jl")
include("padic_prime_search.jl")
include("cartan.jl")
