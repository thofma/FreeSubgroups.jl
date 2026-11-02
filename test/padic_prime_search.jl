using Test, Random, FreeSubgroups

@testset "Complete p-adic prime search" begin
  FS = FreeSubgroups
  A = matrix(QQ, 2, 2, [1, 1//2, 0, 1])
  B = transpose(A)
  G = matrix_group(A, B)

  @testset "Candidate primes include inverses" begin
    D = diagonal_matrix(QQ.([2, 3]))
    U = matrix(QQ, 2, 2, [1, 1//5, 0, 1])
    @test denominator(D) == 1
    @test FS._padic_candidate_primes([D], [inv(D)]) == ZZ.([2, 3])
    @test FS._padic_candidate_primes([D, U], [inv(D), inv(U)]) == ZZ.([2, 3, 5])
    @test FS._padic_candidate_primes([D], [inv(D)]; small_only = true) == ZZ.([2, 3])
  end

  @testset "Small-prime random witness" begin
    Random.seed!(20261020)
    GAP.Globals.Reset(GAP.Globals.GlobalMersenneTwister, 20261020)
    H = matrix_group(diagonal_matrix(QQ.([3, 1//3])))
    witness = FS._find_unbounded_padic_prime(H; random_samples = 20, radius = 2)
    @test witness !== nothing
    @test witness.source == :small_prime
    @test witness.prime == 3
    @test map_word(witness.word, gens(H)) == witness.element
    @test valuation(trace(witness.element), 3) < 0

    explicit = FS._find_unbounded_padic_prime(H; p = 3, random_samples = 20, radius = 2)
    @test explicit.source == :random
    @test explicit.prime == 3
    @test map_word(explicit.word, gens(H)) == explicit.element
  end

  @testset "Fast witness with a large unfactored cofactor" begin
    # find 3 without factoring the large Mersenne-prime factors
    q = 3 * (ZZ(2)^127 - 1) * (ZZ(2)^107 - 1)
    D = diagonal_matrix(QQ.([q, 1//q]))
    @test FS._padic_candidate_primes([D], [inv(D)]; small_only = true) == ZZ.([3])
    H = matrix_group(D)
    Random.seed!(20261030)
    GAP.Globals.Reset(GAP.Globals.GlobalMersenneTwister, 20261030)
    witness = FS._find_unbounded_padic_prime(H; random_samples = 20, radius = 2)
    @test witness !== nothing
    @test witness.source == :small_prime
    @test witness.prime == 3
    @test valuation(trace(witness.element), 3) < 0
    @test map_word(witness.word, gens(H)) == witness.element
  end

  @testset "Full factorization after the small-prime phase" begin
    # conjugation introduces powers of 2, but the eigenvalues are 2-adic units
    # q and r need the full factorization
    q = next_prime(ZZ(10)^9)
    r = next_prime(q)
    C = matrix(QQ, 2, 2, [1, QQ(1, ZZ(2)^32), 0, 1])
    D = diagonal_matrix(QQ.([q*r, 1//(q*r)]))
    M = inv(C) * D * C
    H = matrix_group(M)
    @test FS._padic_candidate_primes([M], [inv(M)]; small_only = true) == ZZ.([2])
    @test FS._padic_candidate_primes([M], [inv(M)]) == ZZ.([2, q, r])
    Random.seed!(20261030)
    GAP.Globals.Reset(GAP.Globals.GlobalMersenneTwister, 20261030)
    witness = FS._find_unbounded_padic_prime(H; random_samples = 20, radius = 2)
    @test witness !== nothing
    @test witness.source == :random
    @test witness.prime == q
    @test valuation(trace(witness.element), q) < 0
    @test valuation(trace(witness.element), 2) >= 0
    @test map_word(witness.word, gens(H)) == witness.element

    exhaustive = FS._find_unbounded_padic_prime(H; random_samples = 0)
    @test exhaustive.source == :exhaustive
    @test exhaustive.prime == q
    @test map_word(exhaustive.word, gens(H)) == exhaustive.element
  end

  @testset "Exhaustive witness and its word" begin
    witness = FS._find_unbounded_padic_prime(G; random_samples = 0)
    @test witness !== nothing
    @test witness.source == :exhaustive
    @test witness.prime == 2
    @test 1 <= length(witness.word) <= degree(G)^2
    @test map_word(witness.word, gens(G)) == witness.element
    @test any(v -> !is_zero(v), FS._root_valuations(charpoly(matrix(witness.element)), witness.prime))
    explicit = FS._find_unbounded_padic_prime(G; p = 2, random_samples = 0)
    @test explicit.prime == 2
    @test map_word(explicit.word, gens(G)) == explicit.element
  end

  @testset "No gap or squarefree condition in prime selection" begin
    H = matrix_group(diagonal_matrix(QQ.([1//2, 1//2])))
    witness = FS._find_unbounded_padic_prime(H; random_samples = 0)
    f = charpoly(matrix(witness.element))
    @test witness.source == :exhaustive
    @test witness.prime == 2
    @test denominator(trace(witness.element)) == 1
    @test !is_squarefree(f)
    @test !first(FS._is_good_element(witness.element, 2))
    @test map_word(witness.word, gens(H)) == witness.element

    # integral coefficients and trace, but a nonunit constant term
    H = matrix_group(diagonal_matrix(QQ.([2, 3])))
    witness = FS._find_unbounded_padic_prime(H; random_samples = 0)
    f = charpoly(matrix(witness.element))
    @test witness.prime == 2
    @test denominator(f) == 1
    @test valuation(constant_coefficient(f), 2) > 0
  end

  @testset "Entire reduced word ball is visited" begin
    matrices = [A, B]
    inverses = inv.(matrices)
    letters = vcat(matrices, inverses)
    words = Set{Tuple}()
    correct_products = true
    result = FS._visit_reduced_matrix_words(matrices, inverses, 4) do X, path
      push!(words, Tuple(path))
      product = one(parent(A))
      for j in path
        product *= letters[j]
      end
      correct_products &= X == product
      return nothing
    end
    @test result === nothing
    @test correct_products
    @test length(words) == 160 # 4 + 12 + 36 + 108, excluding the identity
    @test [count(w -> length(w) == k, words) for k in 1:4] == [4, 12, 36, 108]
    inverse_letter(j) = j <= 2 ? j + 2 : j - 2
    @test all(w -> all(w[i+1] != inverse_letter(w[i]) for i in 1:length(w)-1), words)
  end

  @testset "Certified bounded outcomes" begin
    # conjugate to SL(2,Z); denominator 2, but all characteristic polynomials integral
    C = matrix(QQ, 2, 2, [1, 0, 2, 1])
    H = matrix_group(A, C)
    @test FS._padic_candidate_primes([A, C], [inv(A), inv(C)]) == ZZ.([2])
    @test FS._find_unbounded_padic_prime(H; random_samples = 0) === nothing
    @test FS._find_unbounded_padic_prime(H; p = 2, random_samples = 0) === nothing
    @test FS._find_unbounded_padic_prime(G; p = 5, random_samples = 0) === nothing
    @test_throws r"bounded at every finite prime" find_free_pair_conjugator_padic(H; startrad = 1)
    @test_throws r"bounded at p = 2" find_free_pair_conjugator_padic(H; p = 2, startrad = 1)
    Igroup = matrix_group(matrix(QQ, 2, 2, [1, 1, 0, 1]), matrix(QQ, 2, 2, [1, 0, 1, 1]))
    @test FS._find_unbounded_padic_prime(Igroup; random_samples = 0) === nothing
    @test_throws r"bounded at every finite prime" find_free_pair_conjugator_padic(Igroup)
    @test_throws ArgumentError FS._find_unbounded_padic_prime(G; p = 4)
    @test_throws ArgumentError FS._find_unbounded_padic_prime(G; random_samples = -1)
    @test_throws ArgumentError FS._find_unbounded_padic_prime(G; radius = 0)
  end
end
