module FreeSubgroups

using Reexport

using LinearAlgebra

@reexport using Oscar

struct LowPrecisionError <: Exception
end

include("basic.jl")
include("archimedean.jl")
include("biproximal.jl")
include("padic.jl")
include("conjugator.jl")
include("sample.jl")
include("svd.jl")
include("examples.jl")
include("optim.jl")

export is_semisimple_biproximal
export can_compute_bound
export biproximal_algorithm
export conjugator_algorithm
export padic_algorithm
export svd_algorithm
export can_compute_biproximal_bound
export biproximal_bound
export burau_representation
export random_subgroup_sln
export random_subgroup_gln

end # module FreeSubgroups
