using Test, FreeSubgroups

@testset "Verified archimedean conjugator bounds" begin
  original_precision = precision(Balls)
  try
    x = diagonal_matrix(QQ.([2, 1//2]))
    for prec in (32, 128), m in (10, 40, 80)
      set_precision!(Balls, prec)
      q = ZZ(2)^m
      b = matrix(QQ, 2, 2, [1, q, q, 1 + q^2])
      # delta^2 = 1/((1+q^2)*(q^4+3*q^2+1)). In dimension two,
      # E = 2*log_2(2*(1+q^2)*(q^4+3*q^2+1)), whose ceiling is 12*m+3.
      @test bound_conjugator(x, b) == 12*m + 3
      @test precision(Balls) == prec
    end

    for t in (17, 101, 1009)
      A, _, b = burau_representation(t = t)
      @test bound_conjugator(A, b) == (t == 17 ? 14 : t == 101 ? 12 : 11)
      @test precision(Balls) == 128
    end
    @test_throws r"Could not verify" bound_conjugator(x, one(parent(x)))
    @test precision(Balls) == 128

    A, B, _ = burau_representation(t = 17)
    G = matrix_group(A, B)
    Oscar.randseed!(20261028)
    result = FreeSubgroups._random_conjugator(G, gen(G,1))
    @test length(result) == 4
    fl, b, wb, cached_bound = result
    @test fl
    @test map_word(wb, gens(G)) == b
    @test cached_bound == bound_conjugator(gen(G,1), b)
    @test precision(Balls) == 128
    @test FreeSubgroups._random_conjugator(G, gen(G,1); maxrad = 0) ==
          (false, gen(G,1), 0, 0)
  finally
    set_precision!(Balls, original_precision)
  end
end
