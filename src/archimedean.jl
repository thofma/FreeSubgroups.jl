################################################################################
#
#  Linear algebra over archimedean fields
#
################################################################################

function l2norm(vec::Vector{ComplexFieldElem})
  d = sum(abs(vec[i])^2 for i in 1:length(vec))
  if !is_nonnegative(d)
    # throw an error indicating that we have not enough precision to determine
    # the norm
    throw(LowPrecisionError)
  end
  return sqrt(d)
end

# distance between vec and the hyperplance with normal vector normvec
function dist_vector_normal_vector(vec::Vector, normvec::Vector)
  @assert length(vec) == length(vec)
  ss = abs(dot(vec, normvec)) # abs(sum(vec1[i]*vec2[i] for i in 1:length(vec1)))
  return ss/(l2norm(vec) * l2norm(normvec))
end

# given a basis of a hyerplane, find a normal vector
function normal_vector(A::MatElem)
  # the rows give the basis
  n = nrows(A)
  @assert n == ncols(A) - 1
  return [inv(A[:, 1:nrows(A)]) * A[:, ncols(A)]; base_ring(A)(-1)]
end

# Return (v, lambda, H), where
# - v is an eigenvector of mat with largest eigenvalue
#   (the Eigenspace is 1-dimensional by assumption)
# - lambda are the eigenvalues, sorted by absolute value
# - A normal vector for the hyperspace spanned by the remaining
#   eigenspaces
function archimedean_eigenspace_data(mat)
  # fields
  CC = complex_field()
  Qb = algebraic_closure(QQ)
  Qm = Qb.(mat)
  # get eigenvalue and top eigenspace over Qb
  lam = eigenvalues(Qb, Qm)
  sort!(lam; by = abs, rev = true)
  # lam[1] is the largest eigenvalue
  es = eigenspace(Qm, lam[1])
  @assert nrows(es) == 1
  esv = es[1, :]
  # basis of the other eigenvalues
  Es = reduce(vcat, [eigenspace(Qm, lam[i]) for i in 2:length(lam)])
  hs = normal_vector(CC.(Es))
  #hs = transpose(hs)
  # return result over C
  return CC.(esv), lam, hs
end
