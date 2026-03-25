################################################################################
#
#  Linear algebra over archimedean fields
#
################################################################################

function isolated_biproximal_eigenvalues_sorted_by_absolute_value(g; prec = 64)
  CC = complex_field()
  d = nrows(g)
  oldprec = precision(Balls)
  if !_is_semisimple(g)
    return false
  end
  while true
    if prec > 2^12
      # precision is getting too large, something might be ood
      break
    end
    set_precision!(Balls, prec)
    local r
    try 
      r = eigenvalues(CC, g)
    catch e
      if e isa ErrorException && startswith(e.msg, "unable")
        prec *= 2
        continue
      end
      rethrow(e)
    end
    if length(r) < d
      return false
    end
    @assert is_pairwise(!overlaps, r)
    rabs = abs.(r)
    sort!(r; by = abs, rev = true)
    if all(i -> rabs[1] > rabs[i], 2:length(rabs)) && all(i -> rabs[i] > rabs[end], 1:length(rabs)-1)
      set_precision!(Balls, oldprec)
      return r
    end
    prec = 2 * prec
  end
  # have to do it precisely
  rr = eigenvalues(algebraic_closure(QQ), g)
  rrabs = abs.(rr)
  p = sortperm(rrabs; rev = true )
  rr = rr[p]
  r = CC.(rr)
  rabs = abs.(r)
  @assert all(i -> rabs[1] > rabs[i], 2:length(rabs)) && all(i -> rabs[i] > rabs[end], 1:length(rabs)-1)
  set_precision!(Balls, oldprec)
  return r
end

function l2norm(vec::Vector{T}) where {T <: Union{RealFieldElem, ComplexFieldElem}}
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
  v = kernel(A; side = :right)
  @assert ncols(v) == 1
  return v[:, 1]
end

acb_to_cc(e, x) = begin
  z = complex_field()()
  @ccall Nemo.libflint.acb_set(z::Ref{ComplexFieldElem}, e(x, precision(Balls))::Ref{AcbFieldElem})::Cvoid
  return z
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
  # get eigenvalue and top eigenspace over Qb
  lam = Oscar.roots(Qb, characteristic_polynomial(mat))
  set_precision!(Balls, 1024) do
    sort!(lam; by = x -> abs(CC(x)), rev = true)
  end
  if !all(i -> abs(CC(lam[1])) > abs(CC(lam[i])), 2:length(lam))
    @info "interesting example"
    # have to resort to complicated sorting in QQbar
    sort!(lam; by = x -> abs(x), rev = true)
  end
  # lam[1] is the largest eigenvalue
  # compute by going to QQ(lam[1])
  K, KtoQQbar = QQ[lam[1]]
  lamK = KtoQQbar\(lam[1])
  # @info "" lam 
  es = eigenspace(map_entries(K, mat), KtoQQbar\(lam[1]))
  mu = change_base_ring(K, minpoly(mat); cached = false)
  g = divexact(mu, gen(parent(mu)) - lamK)
  Es = kernel(g(mat)) # the sum of the other eigenspaces
  @assert nrows(Es) == nrows(mat) - 1
  hs = normal_vector(Es)
  # result over C
  # find the correct embedding K -> C
  embs = complex_embeddings(K)
  found = false
  ee = embs[1]
  for e in embs
    z = CC()
    @ccall Nemo.libflint.acb_set(z::Ref{ComplexFieldElem}, e(lamK, precision(Balls))::Ref{AcbFieldElem})::Cvoid
    if overlaps(z, CC(lam[1]))
      @assert !found
      ee = e
      found = true
    end
  end
  return (acb_to_cc.(Ref(ee), es))[1, :], lam, acb_to_cc.(Ref(ee), hs)
end

function archimedean_eigenspace_data2(mat)
  # fields
  CC = complex_field()
  Qb = algebraic_closure(QQ)
  Qm = Qb.(mat)
   #get eigenvalue and top eigenspace over Qb
   lam = eigenvalues(Qb, mat)
   sort!(lam; by = abs, rev = true)
   # lam[1] is the largest eigenvalue
   # compute by going to QQ(lam[1])
   K, KtoQQbar = QQ[lam[1]]
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
