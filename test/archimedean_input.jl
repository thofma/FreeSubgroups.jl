using Test, FreeSubgroups

@testset "Archimedean coefficient embeddings" begin
  @testset "Explicit complex embedding" begin
    K, i = quadratic_field(-1)
    E, ei = Hecke.embedded_field(K, first(complex_embeddings(K)))
    x = matrix(E, 2, 2, [2, ei, 0, 1//2])
    b = matrix(E, 2, 2, [1, 0, ei, 1])
    y = inv(b)*x*b
    G = matrix_group(x, b)
    before = precision(Balls)

    # reject complex coefficient embeddings before computing bounds or sampling
    for f in (
        () -> FreeSubgroups.archimedean_eigenspace_data(x),
        () -> FreeSubgroups.archimedean_eigenspace_data2(x),
        () -> FreeSubgroups.onorm(x),
        () -> FreeSubgroups.can_compute_biproximal_bound(x, y),
        () -> FreeSubgroups.can_compute_biproximal_bound(x, y; check = false),
        () -> FreeSubgroups.bound_biproximal(x, y),
        () -> FreeSubgroups.bound_conjugator(x, b),
        () -> FreeSubgroups.is_conjugator(G(x), G(b)),
        () -> FreeSubgroups.find_free_pair_biproximal(G),
        () -> FreeSubgroups.find_free_pair_conjugator(G),
        () -> FreeSubgroups.find_free_pair_svd(G),
        () -> FreeSubgroups.operator_norm(x),
        () -> FreeSubgroups._compute_vgs(x),
        () -> FreeSubgroups._transform_normal(complex_field().([1, 0]), x),
    )
      @test_throws ArgumentError f()
    end
    @test precision(Balls) == before
    err = try
      FreeSubgroups.onorm(x)
      nothing
    catch e
      e
    end
    @test err isa ArgumentError
    @test occursin("complex coefficient embeddings are not supported", sprint(showerror, err))

    # also check the number-field wrappers
    raw = matrix_group(matrix(K, 2, 2, [2, i, 0, 1//2]), matrix(K, 2, 2, [1, 0, i, 1]))
    for search in (FreeSubgroups.find_free_pair_biproximal, FreeSubgroups.find_free_pair_conjugator, FreeSubgroups.find_free_pair_svd)
      @test_throws ArgumentError search(raw)
    end

    # keep the embedding for QQbar inputs
    Qb = algebraic_closure(QQ)
    ix = sqrt(Qb(-1))
    xb = matrix(Qb, 2, 2, [2, ix, 0, 1//2])
    bb = matrix(Qb, 2, 2, [1, 0, ix, 1])
    Gb = matrix_group(xb, bb)
    @test_throws ArgumentError FreeSubgroups.onorm(xb)
    for search in (FreeSubgroups.find_free_pair_biproximal, FreeSubgroups.find_free_pair_conjugator, FreeSubgroups.find_free_pair_svd)
      @test_throws ArgumentError search(Gb)
    end
  end

  @testset "Real coefficients with complex eigenvalues" begin
    x = QQ[4 0 0 0; 0 0 -1 0; 0 1 0 0; 0 0 0 1//4]
    b = matrix(QQ, 4, 4, [QQ(1, i+j) for i in 1:4 for j in 1:4])
    R, t = polynomial_ring(QQ, :t)
    K, a = number_field(t^3 - 2; cached = false)
    E, _ = Hecke.embedded_field(K, first(real_embeddings(K)))

    # use the chosen embedding, not the signature of the field
    nonreal = first(e for e in complex_embeddings(K) if !Hecke.is_real(e))
    EC, _ = Hecke.embedded_field(K, nonreal)
    @test_throws ArgumentError FreeSubgroups.onorm(EC.(x))

    for (M, B) in ((x, b), (E.(x), E.(b)))
      @test FreeSubgroups.is_biproximal(M)
      u, values, c = FreeSubgroups.archimedean_eigenspace_data(M)
      @test count(z -> !isreal(z), values) == 2
      @test !contains_zero(FreeSubgroups._dot(u, c))
      @test overlaps(FreeSubgroups.onorm(M), real_field()(4))
      fl, n = FreeSubgroups.can_compute_biproximal_bound(M, inv(B)*M*B)
      @test fl
      @test n > 0
      @test FreeSubgroups.bound_conjugator(M, B) > 0
    end
    @test overlaps(FreeSubgroups.operator_norm(x), real_field()(4))
    vg, vgt = FreeSubgroups._compute_vgs(x)
    @test all(contains_zero, vg[2:end])
    @test all(contains_zero, vgt[2:end])
  end
end
