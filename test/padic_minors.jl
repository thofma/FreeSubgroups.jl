using Test, Random, FreeSubgroups

@testset "P-adic maximal-minor norms" begin
  FS = FreeSubgroups
  rng = Random.Xoshiro(20261030)

  @testset "Agreement with exhaustive exact minors" begin
    for p in (2, 3, 5), d in 2:7, r in 1:d, _ in 1:2
      Qp = padic_field(p; precision = 80, cached = false)
      M = matrix(ZZ, r, d, rand(rng, -20:20, r*d))
      rank(M) == r || continue
      for i in 1:r
        scale = ZZ(p)^rand(rng, 0:8)
        for j in 1:d
          M[i, j] *= scale
        end
      end
      expected = maximum(FS.abs_val(m, p) for m in minors(M, r))
      A = change_base_ring(Qp, M)
      original = deepcopy(A)
      @test FS._padic_maximal_minor_abs(A) == expected
      @test A == original
    end
  end

  @testset "Dependent reductions and precision limits" begin
    for p in (2, 3, 5)
      Qp = padic_field(p; precision = 40, cached = false)
      m = 10
      A = matrix(Qp, 2, 3, [1, 0, 0, 1, ZZ(p)^m, 0])
      B = matrix(Qp, 1, 3, [0, 0, 1])
      @test FS._padic_maximal_minor_abs(A) == QQ(p)^(-m)
      @test FS.distance_of_spaces(A, B) == 1
      @test_throws FS.LowPrecision FS._padic_maximal_minor_abs(map_entries(x -> setprecision(x, m), A))
      @test_throws FS.LowPrecision FS._padic_maximal_minor_abs(matrix(Qp, 2, 3, [1, 0, 0, 1, 0, 0]))
      uncertain = matrix(Qp, 2, 2, [1, O(Qp, ZZ(p)^0), O(Qp, ZZ(p)^0), 1])
      @test_throws FS.LowPrecision FS._padic_maximal_minor_abs(uncertain)
      @test FS._padic_maximal_minor_abs(zero_matrix(Qp, 0, 3)) == 1
    end
  end

  @testset "Complementary 9- and 10-dimensional spaces in dimension 19" begin
    # the fraction-free determinant needs 800 bits for these nearly dependent rows
    Qp = padic_field(2; precision = 800, cached = false)
    A = zero_matrix(Qp, 9, 19)
    for i in 1:9
      A[i, 1] = 1
      i > 1 && (A[i, i] = ZZ(2)^i)
    end
    B = zero_matrix(Qp, 10, 19)
    for i in 1:10
      B[i, 9+i] = 1
    end
    @test FS._padic_maximal_minor_abs(A) == QQ(2)^(-sum(2:9))
    @test FS.distance_of_spaces(A, B) == 1
  end
end
