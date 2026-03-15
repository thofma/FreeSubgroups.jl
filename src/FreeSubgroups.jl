module FreeSubgroups

using Reexport

@reexport using Oscar

struct LowPrecisionError <: Exception
end

include("basic.jl")
include("archimedean.jl")
include("biproximal.jl")
include("padic.jl")
include("conjugator.jl")

end # module FreeSubgroups
