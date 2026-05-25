module FreeSubgroups

function __init__()
  add_verbosity_scope(:FreeSubgroups)
end

using Reexport

using LinearAlgebra

@reexport using Oscar

struct LowPrecisionError <: Exception
end

include("basic.jl")
include("archimedean.jl")
include("pingpong.jl")
include("biproximal.jl")
include("padic.jl")
include("conjugator.jl")
include("sample.jl")
include("svd.jl")
include("svd_padic.jl")
include("examples.jl")
include("optim.jl")

export bound_biproximal
export bound_conjugator
export bound_conjugator_padic
export verify_free_pair_cones

export find_free_pair_biproximal
export find_free_pair_conjugator
export find_free_pair_conjugator_padic
export find_free_pair_svd
export find_free_pair_cartan

export can_compute_biproximal_bound
export burau_representation
export random_subgroup_sln
export random_subgroup_gln
export is_biproximal

end # module FreeSubgroups
