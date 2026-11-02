# examples from the dimension benchmark
using FreeSubgroups, Random, Test

@testset "Reported dimension benchmark" begin
  original_precision = precision(Balls)
  for n in (7, 9)
    seed = 2026 + 1000*n + 1
    rng = Random.Xoshiro(seed)
    matrices = QQMatrix[]
    # the same SL(n, QQ) inputs as in the benchmark
    for _ in 1:2
      while true
        M = matrix(QQ, n, n, [QQ(rand(rng, -20:20), rand(rng, 1:20)) for _ in 1:n^2])
        d = det(M)
        is_zero(d) && continue
        for j in 1:n
          M[1, j] = M[1, j] // d
        end
        @test is_one(det(M))
        push!(matrices, M)
        break
      end
    end
    G = matrix_group(matrices)

    if n == 9
      x = gen(G,1) * gen(G,2)^2
      @test FreeSubgroups.is_semisimple_biproximal(x)
      Random.seed!(seed)
      GAP.Globals.Reset(GAP.Globals.GlobalMersenneTwister, seed)
      fl, b, wb, bound = FreeSubgroups._random_conjugator(G, x; prec=32, maxrad=3)
      @test fl
      @test map_word(wb, gens(G)) == b
      @test bound > 0
      @test precision(Balls) == original_precision
    end

    for method in (find_free_pair_conjugator, find_free_pair_svd)
      @testset "$n: $method" begin
        Random.seed!(seed)
        GAP.Globals.Reset(GAP.Globals.GlobalMersenneTwister, seed)
        result = method(G)
        (x, b), (wx, wb) = result[1], result[2]
        @test map_word(wx, gens(G)) == x
        @test map_word(wb, gens(G)) == b
        @test max(length(wx), length(wx^wb)) > 0
        if method === find_free_pair_conjugator
          @test result[3] > 0
        end
        @test precision(Balls) == original_precision
      end
    end
  end
end
