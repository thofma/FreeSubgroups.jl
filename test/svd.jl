using Test, FreeSubgroups

@testset "SVD interval directions and spectral reuse" begin
  FS = FreeSubgroups
  original_precision = precision(Balls)
  try
    @testset "Rational left eigenvectors and defining covectors" begin
      for prec in (32,128), m in (
          matrix(QQ,3,3,[5,2,1,0,2,1,1,0,-1]),
          matrix(QQ,3,3,[-5,2,1,0,2,1,1,0,1]))
        set_precision!(Balls,prec)
        u, lam, normal = FS.archimedean_eigenspace_data(m)
        exact_u, _, exact_normal = invoke(FS._archimedean_eigenspace_data,
                                          Tuple{Any,Any},m,lam)
        a = complex_field().(m)
        lambda = complex_field()(lam[1])
        @test all(contains_zero,u*a-lambda.*u)
        @test all(contains_zero,normal*transpose(a)-lambda.*normal)
        @test all(contains_zero(u[i]*exact_u[j]-u[j]*exact_u[i])
                  for i in eachindex(u), j in eachindex(u))
        @test all(contains_zero(normal[i]*exact_normal[j]-normal[j]*exact_normal[i])
                  for i in eachindex(normal), j in eachindex(normal))
        @test precision(Balls) == prec
      end
    end

    examples = [
      identity_matrix(QQ, 3),
      diagonal_matrix(QQ.([10, 1, 1, 1//10])),
      matrix(QQ, 3, 3, [3, 2, 1, 0, 2, 1, 1, 0, 1]),
    ]
    for prec in (64, 128), g in examples
      set_precision!(Balls, prec)
      ev = FS._eigenvalues_of_ggt(g)
      @test overlaps(FS.rho(g; evs=ev[1]), min(FS.beta(g), FS.beta(inv(g))))
      @test overlaps(FS.lipschitz_const(g; evs=ev[1]),
                     (FS.operator_norm(g) * FS.operator_norm(inv(g)))^2)
      @test overlaps(FS.epsilon(g; ev), FS.rho(g)^(-1//2))
      for a in (g, inv(g))
        h = a * transpose(a)
        e = FS._eigenvalues(h)
        v = FS._eigenvector_of_largest_eigenvalue(h, e)
        # compare with the exact number-field computation
        exact = invoke(FS._eigenvector_of_largest_eigenvalue,
                       Tuple{MatElem, Any}, h, e)
        @test all(contains_zero, v * real_field().(h) - e[1][1] .* v)
        @test all(contains_zero(v[i]*exact[j] - v[j]*exact[i])
                  for i in eachindex(v), j in eachindex(v))
        vg, vgt = FS._compute_vgs(a)
        @test all(contains_zero, vg * real_field().(transpose(a)*a) - e[1][1] .* vg)
        @test all(contains_zero, vgt * real_field().(h) - e[1][1] .* vgt)
      end
      @test precision(Balls) == prec
    end

    # the smallest singular value needs more than 64 bits
    set_precision!(Balls, 64)
    q = QQ(ZZ(2)^80)
    g = matrix(QQ, 2, 2, [q, q, q, q+inv(q)])
    values, _ = FS._eigenvalues_of_ggt(g)
    @test all(is_positive, values)
    @test all(x -> accuracy_bits(x) >= 32, values)
    @test contains(values[1]*values[2], 1) # det(g*g^T) = 1
    @test precision(Balls) == 64

    close = diagonal_matrix(QQ.([1 + 1//ZZ(2)^100, 1, 1//2]))
    values, _ = FS._eigenvalues_of_ggt(close)
    @test values[1] > values[2] > values[3]
    @test precision(Balls) == 64

    g = diagonal_matrix(QQ.([ZZ(10)^20, 1//ZZ(10)^20]))
    z = matrix(QQ, 2, 2, [1, 1, 1, 2])
    b = matrix(QQ, 2, 2, [1, 2, 1, 3])
    fl, ax, axbar, Bx, Bxbar = FS._check_z(g, z)
    @test fl
    @test FS._check_b(g, z, b, ax, axbar, Bx, Bxbar)
    G = matrix_group(g, z, b)
    x = gen(G,1) * gen(G,2)
    @test verify_free_pair_cones(G, x, x^gen(G,3), 1)
    @test precision(Balls) == 64
  finally
    set_precision!(Balls, original_precision)
  end
end
