using Test, Random, FreeSubgroups

@testset "Implementation corrections" begin
  oldprec = precision(Balls)
  try
    @testset "Returned conjugator words" begin
      Random.seed!(20261020)
      GAP.Globals.Reset(GAP.Globals.GlobalMersenneTwister, 20261020)
      A, B, _ = burau_representation(t = 17)
      G = matrix_group(A, B)
      for search in (FreeSubgroups.find_free_pair_conjugator, FreeSubgroups.find_free_pair_conjugator_padic)
        before = precision(Balls)
        (x, b), (wx, wb), l = search(G; stab = 1)
        @test map_word(wx, gens(G)) == x
        @test map_word(wb, gens(G)) == b
        @test l > 0
        @test precision(Balls) == before
      end
    end

    @testset "Coefficient field and embedding" begin
      F, _ = quadratic_field(2)
      Qb = algebraic_closure(QQ)
      CC = complex_field()
      for (j, emb) in enumerate(real_embeddings(F))
        E, a = Hecke.embedded_field(F, emb)
        matrices = [
          diagonal_matrix(E.([3, a, 1//3])),
          matrix(E, 3, 3, [3, a, 0, 0, 1, 0, 0, 0, 1//3]),
          matrix(E, 2, 2, [0, 1, 1, a]),
        ]
        for (i, M) in enumerate(matrices)
          @testset "Embedding $j matrix $i" begin
            @test FreeSubgroups.is_biproximal(M)
            u, lambdas, c = FreeSubgroups.archimedean_eigenspace_data(M)
            MC = CC.(Qb.(M))
            lambda = CC(lambdas[1])
            @test all(contains_zero, u * MC - lambda .* u)
            @test all(r -> contains_zero(sum(MC[r,s] * c[s] for s in 1:ncols(M)) - lambda*c[r]), 1:nrows(M))
            @test !contains_zero(FreeSubgroups._dot(u, c))
            if i == 2
              @test contains_zero(2*u[2] - CC(Qb(a))*u[1])
            elseif i == 3
              K, ktoQQbar = FreeSubgroups._eigenvalue_field(E, lambdas[1])
              @test degree(K) == 4
              e = FreeSubgroups._embed(E, K, ktoQQbar)
              @test ktoQQbar(e(a)) == Qb(a)
              @test ktoQQbar(ktoQQbar\lambdas[1]) == lambdas[1]
            end
          end
        end
      end
      @testset "Bound over a genuine number field" begin
        E, a = Hecke.embedded_field(F, first(real_embeddings(F)))
        A, B, _ = burau_representation(t = 17)
        S = matrix(E, 3, 3, [1, a, 0, 0, 1, 0, 0, 0, 1])
        x, y = inv(S) * E.(A) * S, inv(S) * E.(B) * S
        fl, l = FreeSubgroups.can_compute_biproximal_bound(x, y)
        @test fl
        @test l > 0
      end
    end

    @testset "Factored singular spectrum" begin
      examples = [
        diagonal_matrix(QQ.([10, 1, 1//10])),
        diagonal_matrix(QQ.([10, 1, 1, 1//10])),
        matrix(QQ, 3, 3, [1, 0, 0, 0, 2, 1, 0, 1, 1]),
      ]
      for (i, g) in enumerate(examples)
        h = transpose(g) * g
        values, factors = FreeSubgroups._eigenvalues(h)
        @test length(values) == nrows(g)
        @test length(factors) == nrows(g)
        @test all(contains_zero(f(v)) for (f,v) in zip(factors,values))
        if i <= 2
          expected = i == 1 ? QQ.([100, 1, 1//100]) : QQ.([100, 1, 1, 1//100])
          @test all(overlaps(v, real_field()(w)) for (v,w) in zip(values,expected))
          @test overlaps(FreeSubgroups.rho(g), real_field()(10))
        end
        v = FreeSubgroups._eigenvector_of_largest_eigenvalue(h, (values,factors))
        @test all(contains_zero, v * real_field().(h) - values[1] .* v)
      end
    end

    @testset "Precision restoration" begin
      A, B, _ = burau_representation(t = 17)
      G = matrix_group(A, B)
      singular = diagonal_matrix(QQ.([3, 1, 0]))
      one_dimensional = matrix_group(matrix(QQ, 1, 1, [2]))
      for requested in (80, 192)
        set_precision!(Balls, requested)
        @test FreeSubgroups.can_compute_biproximal_bound(A, B) == (true, 14)
        @test precision(Balls) == requested
        @test FreeSubgroups.can_compute_biproximal_bound(A, A) == (false, -1)
        @test precision(Balls) == requested
        @test_throws r"^Matrix not invertible$" FreeSubgroups.can_compute_biproximal_bound(singular, B)
        @test precision(Balls) == requested
        @test !first(FreeSubgroups._random_conjugator(G, G(A); maxrad = 0))
        @test precision(Balls) == requested
        # no second singular value or eigenvalue in dimension 1
        @test_throws BoundsError FreeSubgroups.find_free_pair_svd(one_dimensional)
        @test precision(Balls) == requested
        @test_throws BoundsError FreeSubgroups.is_biproximal(matrix(QQ, 1, 1, [2]))
        @test precision(Balls) == requested
      end
    end
  finally
    set_precision!(Balls, oldprec)
  end
end
