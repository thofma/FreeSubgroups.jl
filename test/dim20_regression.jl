# dimension 20 examples from the timing report
# Run from the package root: julia --project=. test/dim20_regression.jl
using FreeSubgroups, Test

module Dim20FirstExample
using FreeSubgroups
include(joinpath(@__DIR__, "Dim20.jl"))
end

module Dim20SecondExample
using FreeSubgroups
include(joinpath(@__DIR__, "Dim20b.jl"))
end

@testset "Reported dimension-20 examples" begin
  original_precision = precision(Balls)
  G = Dim20FirstExample.G
  x = inv(gen(G,1)) * gen(G,2)
  b = gen(G,2) * inv(gen(G,1))
  # this pair needs more than 128 bits for delta
  @test can_compute_biproximal_bound(x, x^b) == (true, 306)
  @test bound_conjugator(x, b) == 306
  @test precision(Balls) == original_precision

  for (example,G) in (("Dim20",Dim20FirstExample.G), ("Dim20b",Dim20SecondExample.G)),
      seed in (20261028,20261029,20261030), method in (:biproximal,:conjugator)
    Oscar.randseed!(seed)
    result = @timed (method === :biproximal ? find_free_pair_biproximal(G) : find_free_pair_conjugator(G))
    (x,y),(wx,wy),l = result.value
    k = method === :biproximal ? max(length(wx),length(wy)) : max(length(wx),length(wx^wy))
    @info "dimension-20 regression" example seed method seconds=result.time bytes=result.bytes k l
    @test map_word(wx, gens(G)) == x
    @test map_word(wy, gens(G)) == y
    @test l > 0
    @test precision(Balls) == original_precision
  end
end
