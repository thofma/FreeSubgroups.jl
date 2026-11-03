using Test, Random, FreeSubgroups

@testset "Precision failures in the H=10 dimension benchmark" begin
  FS = FreeSubgroups
  for (n, i) in ((9, 6), (11, 1), (13, 1), (15, 1), (15, 3), (28, 4), (37, 4))
    @testset "dimension $n, group $i" begin
      seed = 2026 + 1000*n + i
      rng = Random.Xoshiro(seed)
      matrices = QQMatrix[]
      for _ in 1:2
        while true
          M = matrix(QQ, n, n, [QQ(rand(rng, -10:10), rand(rng, 1:10)) for _ in 1:n^2])
          d = det(M)
          is_zero(d) && continue
          for j in 1:n
            M[1, j] = M[1, j] // d
          end
          push!(matrices, M)
          break
        end
      end
      A, B = matrices
      if n == 9 || i == 3
        # group 3 used to give a negative precision exponent in Hecke.fun_factor
        G = matrix_group(matrices)
        Random.seed!(seed)
        GAP.Globals.Reset(GAP.Globals.GlobalMersenneTwister, seed)
        (x, b), (wx, wb), bound = find_free_pair_conjugator_padic(G; p = 2)
        @test map_word(wx, gens(G)) == x
        @test map_word(wb, gens(G)) == b
        @test bound > 0
      else
        # failing search words: nonintegral element (11), Newton polygon (13),
        # empty factors (15), exact division at precision 400 (28), powering (37)
        x, b = if n == 11
          inv(A)*inv(B)*inv(A)*B*inv(A), inv(B)
        elseif n == 13
          inv(B)^3*inv(A), inv(A)^2*B
        elseif n == 28
          (A*B)^2*inv(A), inv(B)*inv(A)^2
        elseif n == 37
          inv(A)*inv(B)*inv(A), inv(A)^2
        else
          B*A*inv(B)*A, inv(B)*A
        end
        @test first(FS._is_good_element(x, 2))
        @test_throws FS.LowPrecision FS._padic_slope_spaces(x, 2; prec = n == 28 ? 400 : 100)
        @test FS.can_compute_bound_conjugator_padic(x, b, 2; maxprec = 100) == (false, -1)
        if n == 13 || n == 37
          @test FS.can_compute_bound_conjugator_padic(x, b, 2) == (false, -1)
        else
          data = FS.compute_delta(x, b, 2; prec = 1600)
          @test data.delta == QQ(2)^(-(n == 11 ? 25 : n == 28 ? 293 : 14))
          bound = bound_conjugator_padic(x, b, 2; prec = 1600, maxprec = 1600)
          @test bound > 0
          if n == 28
            @test FS.can_compute_bound_conjugator_padic(x, b, 2) == (false, -1)
            @test FS.can_compute_bound_conjugator_padic(x, b, 2; maxprec = 1600) == (true, bound)
          else
            @test FS.can_compute_bound_conjugator_padic(x, b, 2) == (true, bound)
          end
          @test bound_conjugator_padic(x, b, 2; maxprec = 1600) == bound
        end
      end
    end
  end
end
