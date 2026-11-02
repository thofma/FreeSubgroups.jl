using Test, Random, LinearAlgebra, FreeSubgroups

@testset "Exact p-adic Cartan computations" begin
  FS = FreeSubgroups
  examples = (
    identity_matrix(QQ, 2),
    matrix(QQ, 2, 2, [0, -1//12, 12, 1]),
    diagonal_matrix(QQ.([1//6, 1, 6])),
    matrix(QQ, 3, 3, [3, 2, 1, 0, 2, 1, 1, 0, 1]),
    matrix(QQ, 4, 4, [0, 0, 0, 1//6, 0, 0, 2, 0, 0, 3, 0, 0, -1, 0, 0, 0]),
  )
  @testset "Smith-form references" begin
    for g in examples, p in (2, 3, 5)
      g0 = deepcopy(g)
      M = ZZ.(denominator(g) * g)
      M0 = deepcopy(M)
      # compare with the full Smith transformations
      C = FS._p_adic_svd(g, p)
      Ci = FS._inv(C)
      @test C.U * C.SS * C.V == g
      @test Ci.U * Ci.SS * Ci.V == inv(g)
      @test [FS.sigma(g, i, p) for i in 1:nrows(g)] ==
            [FS.sigma(C, i) for i in 1:nrows(g)]
      @test FS.beta(g, p) == FS.beta(C)
      rho0 = min(FS.beta(C), FS.beta(Ci))
      @test FS.rho(g, p) == rho0
      @test overlaps(FS.epsilon(g, p)^2, real_field()(inv(rho0)))
      @test FS.lip(g, p) == (FS.sigma(C, 1) * FS.sigma(Ci, 1))^2
      @test FS.lip(g, p; ginv = inv(g)) == FS.lip(g, p)
      vgs = FS._cartan_directions(M)
      @test vgs == (QQ.(FS.vg(C)), QQ.(FS.vgprime(C)),
                           QQ.(FS.vg(Ci)), QQ.(FS.vgprime(Ci)))
      @test all(v -> FS._norm_vector(v, p) == 1, vgs)
      v, n, vi, ni = vgs
      @test is_zero(dot(v, ni))
      @test is_zero(dot(vi, n))
      @test g == g0
      @test M == M0
    end
  end

  @testset "Transformed hyperplane normals" begin
    g = diagonal_matrix(QQ.([1//64, 1, 64]))
    z = matrix(QQ, 3, 3, [2, 1, 0, 0, 1, 1, 1, 0, 1])
    zi = inv(z)
    for p in (2, 3, 5)
      C = FS._p_adic_svd(g, p)
      n = QQ.(FS.vgprime(C))
      nz = FS._transform_normal(n, z; hinv = zi)
      H = FS.Hg(C) * z
      @test all(is_zero, H * nz)
      for u in (QQ.([1, 2, 3]), QQ.([3, -1, 4]), QQ.([0, 1, 0]))
        @test FS._padic_dist_vector_normal_vector(u, nz, p) ==
              FS._padic_dist_vector_hypersurface(u, H, p)
      end
    end
  end

  b = matrix(QQ, 3, 3, [1, 1, 1, 1, 2, 3, 1, 3, 6])
  z = identity_matrix(QQ, 3)
  @testset "Exact boundary and odd singular-value gap" begin
    for p in (2, 3), gap in (2, 3)
      g = diagonal_matrix(QQ.([QQ(p)^(-gap), 1, QQ(p)^gap]))
      vgs = FS._cartan_directions(ZZ.(denominator(g) * g))
      eps2 = inv(FS.rho(g, p))
      fl, data = FS._check_cartan_z(z, p, vgs, eps2)
      @test fl
      # gap 2 is the boundary; gap 3 has irrational eps
      @test FS._check_cartan_b(b, p, data, eps2, FS.lip(z, p)) == (gap == 3)
      fl1, data1 = FS.is_z_good_for_g(g, z, p)
      @test fl1
      @test FS.is_b_good(b, z, data1..., FS.epsilon(g, p), p) == (gap == 3)
      zbad = diagonal_matrix(QQ.([QQ(p)^4, 1, QQ(p)^(-4)]))
      @test !first(FS._check_cartan_z(zbad, p, vgs, eps2))
    end
  end

  @testset "Independent cones verification" begin
    g = diagonal_matrix(QQ.([QQ(2)^(-80), 1, QQ(2)^80]))
    G = matrix_group(g, b)
    vgs = FS._cartan_directions(ZZ.(denominator(g) * g))
    fl, data = FS._check_cartan_z(z, 2, vgs, inv(FS.rho(g, 2)))
    @test fl
    @test FS._check_cartan_b(b, 2, data, inv(FS.rho(g, 2)), 1)
    x, conjugator = gens(G)
    @test verify_free_pair_cones(G, x, x^conjugator, 1)
  end

  @testset "Returned search words" begin
    g = diagonal_matrix(QQ.([QQ(2)^(-40), 1, QQ(2)^40]))
    G = matrix_group(g, b)
    Random.seed!(20261030)
    GAP.Globals.Reset(GAP.Globals.GlobalMersenneTwister, 20261030)
    before = precision(Balls)
    (x, conjugator), (wx, wb) = find_free_pair_cartan(G; stab = 1)
    @test map_word(wx, gens(G)) == x
    @test map_word(wb, gens(G)) == conjugator
    @test precision(Balls) == before
    @test_throws ArgumentError find_free_pair_cartan(G; stab = -1)
    @test_throws ArgumentError find_free_pair_cartan(G; startrad = 0)
  end
end
