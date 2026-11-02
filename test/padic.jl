using Test, Random, FreeSubgroups

@testset "Slope factors over Q_p" begin
  FS = FreeSubgroups

  @testset "Small primes and returned words" begin
    A = matrix(QQ, 2, 2, [1, 1//2, 0, 1])
    B = transpose(A)
    x = A * B
    @test FS.has_p_with_symmetric_gap_in_eigenvalues(x) == (true, ZZ(2))
    @test FS._root_valuations(charpoly(x), 2) == QQ.([-2, 2])
    @test bound_conjugator_padic(x, A, 2) == 2
    G = matrix_group(A, B)
    for p in (nothing, 2)
      Random.seed!(20261020)
      GAP.Globals.Reset(GAP.Globals.GlobalMersenneTwister, 20261020)
      (u, b), (wu, wb), n = find_free_pair_conjugator_padic(G; p, stab = 1)
      @test map_word(wu, gens(G)) == u
      @test map_word(wb, gens(G)) == b
      @test n > 0
      @test first(FS._is_good_element(u, 2))
    end
  end

  @testset "Unramified cubic at a common index divisor" begin
    R, t = polynomial_ring(QQ, :t)
    # 2 splits, but no integral primitive generator has discriminant prime to 2
    x = companion_matrix(t^3 - t^2 - 2*t - 8)
    Qp, (A, Rr, Ai, Ri), vals, i0 = FS._padic_slope_spaces(x, 2)
    @test Qp isa PadicField
    @test vals == QQ.([0, 1, 2])
    @test i0 == 1
    @test nrows.((A, Rr, Ai, Ri)) == (1, 2, 1, 2)
    @test all(U -> is_zero(U * change_base_ring(Qp, x) * kernel(U; side = :right)), (A, Rr, Ai, Ri))
    @test !is_zero(det(vcat(A, Rr)))
    @test !is_zero(det(vcat(Ai, Ri)))
  end

  @testset "Ramified eigenvalues without extending Q_p" begin
    R, t = polynomial_ring(QQ, :t)
    x = companion_matrix(t^4 - 1//5*t^3 - 1//125*t^2 + 1)
    b = matrix(QQ, 4, 4, [1,1,2,3, 0,1,1,2, 0,0,1,1, 0,0,0,1])
    @test FS.has_p_with_symmetric_gap_in_eigenvalues(x) == (true, ZZ(5))
    @test FS._root_valuations(charpoly(x), 5) == QQ.([-3//2, -3//2, 3//2, 3//2])
    for prec in (60, 100, 160)
      Qp, spaces, vals, i0 = FS._padic_slope_spaces(x, 5; prec)
      @test Qp isa PadicField
      @test i0 == 2
      @test nrows.(spaces) == (2, 2, 2, 2)
      @test all(U -> base_ring(U) === Qp, spaces)
      data = FS.compute_delta(x, b, 5; prec)
      @test data.delta == QQ(5)^(-12)
      @test data.self_distances == (QQ(1), QQ(1), QQ(1), QQ(1))
      @test bound_conjugator_padic(x, b, 5; prec) == 13
    end
  end

  @testset "Manuscript examples" begin
    for p in (17, 101, 1009)
      A, _, b = burau_representation(t = p)
      @test bound_conjugator_padic(A, b, p) == 5
    end
  end

  @testset "Wild ramification and fractional gaps at 2" begin
    R, t = polynomial_ring(QQ, :t)
    b = matrix(QQ, 4, 4, [1,1,2,3, 0,1,1,2, 0,0,1,1, 0,0,0,1])
    examples = [
      (t^4 - 1//2*t^3 - 1//8*t^2 + 1, QQ.([-3//2, -3//2, 3//2, 3//2]), QQ(2)^(-12), 13),
      ((t^2 - 1//2)*(t - 1)*(t - 2), QQ.([-1//2, -1//2, 0, 1]), QQ(1,16), 25),
    ]
    for (f, vals, delta, n) in examples, prec in (60, 160)
      x = companion_matrix(f)
      data = FS.compute_delta(x, b, 2; prec)
      @test data.valuations == vals
      @test data.delta == delta
      @test bound_conjugator_padic(x, b, 2; prec) == n
      if n == 25
        @test vals[data.i0 + 1] - vals[data.i0] == QQ(1,2)
      end
    end
  end

  @testset "Precision retries, exhaustion and distances" begin
    x = diagonal_matrix(QQ.([2, 1//2]))
    m = 24
    b = matrix(QQ, 2, 2, [1, ZZ(2)^m, ZZ(2)^m, 1 + ZZ(2)^(2*m)])
    @test_throws FS.LowPrecision FS.compute_delta(x, b, 2; prec = 4)
    @test FS.can_compute_bound_conjugator_padic(x, b, 2; prec = 4, maxprec = 128) == (true, m + 1)
    @test FS.can_compute_bound_conjugator_padic(x, b, 2; prec = 4, maxprec = 16) == (false, -1)
    @test_throws ErrorException bound_conjugator_padic(x, b, 2; prec = 4, maxprec = 16)
    @test FS.can_compute_bound_conjugator_padic(x, one(parent(x)), 2; maxprec = 100) == (false, -1)

    Qp = padic_field(2; precision = 8, cached = false)
    U = matrix(Qp, 1, 2, [1, 0]) * Qp(ZZ(2)^40)
    V = matrix(Qp, 1, 2, [0, 1]) * Qp(QQ(2)^(-40))
    @test FS.distance_of_spaces(U, V) == 1
    uncertain = matrix(Qp, 1, 2, [Qp(ZZ(2)^20), O(Qp, ZZ(2)^4)])
    @test_throws FS.LowPrecision FS.distance_of_spaces(uncertain, matrix(Qp, 1, 2, [0, 1]))
  end

  @testset "Unsuitable inputs" begin
    x = diagonal_matrix(QQ.([2, 1//2]))
    @test FS.can_compute_bound_conjugator_padic(one(parent(x)), x, 2) == (false, -1)
    @test FS.can_compute_bound_conjugator_padic(x, x, 5) == (false, -1)
    @test FS.can_compute_bound_conjugator_padic(diagonal_matrix(QQ.([0, 2])), x, 2) == (false, -1)
    @test FS.has_p_with_symmetric_gap_in_eigenvalues(one(parent(x))) == (false, 0)
    @test_throws ArgumentError find_free_pair_conjugator_padic(matrix_group(x); p = 4)
    @test_throws ArgumentError bound_conjugator_padic(x, x, 4)
    @test_throws ArgumentError bound_conjugator_padic(x, x, 2; prec = 0)
  end
end
