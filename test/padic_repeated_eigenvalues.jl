using Test, Random, FreeSubgroups

@testset "Repeated p-adic eigenvalues" begin
  FS = FreeSubgroups

  # this conjugator gives delta = p^(-m), also for Jordan blocks
  block_conjugator(p, m) = begin
    b = identity_matrix(QQ, 2*m)
    for i in 1:m
      b[i, m+i] = 1
      b[m+i, i] = 1
      b[m+i, m+i] = p
    end
    b
  end
  same_row_space(U, V) = nrows(U) == nrows(V) &&
                         is_zero(U * kernel(V; side = :right))

  @testset "Repeated rational roots and Jordan blocks" begin
    for p in (2, 5), m in (2, 3), jordan in (false, true)
      x = diagonal_matrix(vcat(fill(QQ(1, p), m), fill(QQ(p), m)))
      if jordan
        for i in 1:m-1
          x[i, i+1] = 1
          x[m+i, m+i+1] = 1
        end
      end
      b = block_conjugator(p, m)
      vals = vcat(fill(QQ(-1), m), fill(QQ(1), m))
      @test !is_squarefree(charpoly(x))
      @test FS._is_good_element(x, p) == (true, vals)
      @test is_squarefree(minpoly(x)) == !jordan
      for prec in (60, 120)
        Qp, spaces, actual_vals, i0 = FS._padic_slope_spaces(x, p; prec)
        I = identity_matrix(Qp, 2*m)
        A, R = I[1:m, :], I[m+1:2*m, :]
        @test actual_vals == vals
        @test i0 == m
        @test all(same_row_space(U, V) for (U, V) in zip(spaces, (A, R, R, A)))
        X = change_base_ring(Qp, x)
        @test nrows(kernel(X - Qp(QQ(1, p))*I; side = :left)) == (jordan ? 1 : m)
        data = FS.compute_delta(x, b, p; prec)
        @test data.delta == QQ(p)^(-m)
        @test data.self_distances == (QQ(1), QQ(1), QQ(1), QQ(1))
        # ||x||_p=p and ||x^-1||_p=p^(jordan ? m : 1).
        @test bound_conjugator_padic(x, b, p; prec) == (jordan ? m*(m + 1) : 3*m - 1)
      end
    end
  end

  @testset "Different multiplicities and a neutral Jordan block" begin
    for p in (2, 5)
      x = diagonal_matrix(QQ.([QQ(1, p), 1, 1, p]))
      x[2, 3] = 1
      b = matrix(QQ, 4, 4, [1,1,1,1, 1,2,3,4, 1,3,6,10, 1,4,10,20])
      Qp, spaces, vals, i0 = FS._padic_slope_spaces(x, p)
      I = identity_matrix(Qp, 4)
      expected = (I[1:1, :], I[2:4, :], I[4:4, :], I[1:3, :])
      @test vals == QQ.([-1, 0, 0, 1])
      @test i0 == 1
      @test !is_squarefree(minpoly(x))
      @test all(same_row_space(U, V) for (U, V) in zip(spaces, expected))
      @test bound_conjugator_padic(x, b, p) == (p == 2 ? 9 : 7)
    end
  end

  @testset "Repeated ramified roots and generalized eigenspaces" begin
    R, t = polynomial_ring(QQ, :t)
    for p in (2, 5)
      x = zero_matrix(QQ, 8, 8)
      C1 = companion_matrix((t^2 - QQ(1, p))^2)
      C2 = companion_matrix((t^2 - p)^2)
      for i in 1:4, j in 1:4
        x[i, j] = C1[i, j]
        x[4+i, 4+j] = C2[i, j]
      end
      b = block_conjugator(p, 4)
      @test !is_squarefree(minpoly(x))
      for prec in (60, 120)
        Qp, spaces, vals, i0 = FS._padic_slope_spaces(x, p; prec)
        I = identity_matrix(Qp, 8)
        A, Rr = I[1:4, :], I[5:8, :]
        @test vals == vcat(fill(QQ(-1, 2), 4), fill(QQ(1, 2), 4))
        @test i0 == 4
        @test all(same_row_space(U, V) for (U, V) in zip(spaces, (A, Rr, Rr, A)))
        X = change_base_ring(Qp, x)
        @test nrows(kernel(X^2 - Qp(QQ(1, p))*I; side = :left)) == 2
        @test FS.compute_delta(x, b, p; prec).delta == QQ(p)^(-4)
        @test bound_conjugator_padic(x, b, p; prec) == 33
      end
    end
  end

  @testset "Conjugated spaces and precision limits" begin
    T = matrix(QQ, 4, 4, [1,1,1,1, 1,2,3,4, 1,3,6,10, 1,4,10,20])
    @test det(T) == 1
    for p in (2, 5)
      x = diagonal_matrix(QQ.([QQ(1, p), QQ(1, p), p, p]))
      x[1, 2] = x[3, 4] = 1
      b = block_conjugator(p, 2)
      x, b = inv(T)*x*T, inv(T)*b*T
      Qp, spaces, _, _ = FS._padic_slope_spaces(x, p)
      Tp = change_base_ring(Qp, T)
      A, R = Tp[1:2, :], Tp[3:4, :]
      @test all(same_row_space(U, V) for (U, V) in zip(spaces, (A, R, R, A)))
      @test FS.compute_delta(x, b, p; prec = 100).delta == QQ(p)^(-2)
      @test bound_conjugator_padic(x, b, p) == 6
    end

    x = diagonal_matrix(QQ.([1//2, 1//2, 2, 2]))
    q = ZZ(2)^24
    b = identity_matrix(QQ, 4)
    for i in 1:2
      b[i, 2+i] = q
      b[2+i, i] = q
      b[2+i, 2+i] = 1 + q^2
    end
    @test FS.can_compute_bound_conjugator_padic(x, b, 2; prec = 4, maxprec = 256) == (true, 51)
    @test FS.can_compute_bound_conjugator_padic(x, b, 2; prec = 4, maxprec = 16) == (false, -1)
  end

  @testset "Search in a representation with repeated eigenvalues" begin
    A = identity_matrix(QQ, 4)
    B = identity_matrix(QQ, 4)
    A[1, 2] = A[3, 4] = QQ(1, 2)
    B[2, 1] = B[4, 3] = QQ(1, 2)
    G = matrix_group(A, B)
    Random.seed!(20261020)
    GAP.Globals.Reset(GAP.Globals.GlobalMersenneTwister, 20261020)
    (x, b), (wx, wb), n = find_free_pair_conjugator_padic(G; p = 2, stab = 1)
    @test map_word(wx, gens(G)) == x
    @test map_word(wb, gens(G)) == b
    @test !is_squarefree(charpoly(matrix(x)))
    @test first(FS._is_good_element(x, 2))
    @test n == bound_conjugator_padic(x, b, 2)
  end
end
