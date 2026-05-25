using Test, FreeSubgroups

@test 1 == 1
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
  #@test l isa Int
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
  #@test l isa Int
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
  @test l == 3
  #G = matrix_group(QQ, 3, [A, B])
end

include("pingpong.jl")
