################################################################################
#
#  Linear algebra over archimedean fields
#
################################################################################

# check the coefficient embedding
# real matrices can still have complex eigenvalues
function _require_real_archimedean_input(F, coeffs = ())
  fl = if F isa EmbeddedNumField
    Hecke.is_real(Hecke.embedding(F))
  elseif F isa AbsSimpleNumField
    !isempty(real_embeddings(F))
  elseif F isa QQBarField || F isa ComplexField
    all(isreal, coeffs)
  else
    true
  end
  fl || throw(ArgumentError("Archimedean methods require a real coefficient embedding; complex coefficient embeddings are not supported"))
  return nothing
end

_require_real_archimedean_input(A::MatElem) = _require_real_archimedean_input(base_ring(A), A)
_require_real_archimedean_input(g::MatGroupElem) = _require_real_archimedean_input(matrix(g))

function _require_real_archimedean_input(G::MatrixGroup)
  F = base_ring(G)
  _require_real_archimedean_input(F)
  if F isa QQBarField || F isa ComplexField
    for g in gens(G)
      _require_real_archimedean_input(g)
    end
  end
  return nothing
end

function _with_ball_precision(f, prec::Int)
  oldprec = precision(Balls)
  try
    set_precision!(Balls, prec)
    return f()
  finally
    set_precision!(Balls, oldprec)
  end
end

function isolated_biproximal_eigenvalues_sorted_by_absolute_value(g; prec = 64)
  oldprec = precision(Balls)
  try
    CC = complex_field()
    d = nrows(g)
    if !_is_semisimple(g)
      return false
    end
    if is_squarefree(characteristic_polynomial(g))
      while true
        if prec > 2^12
          # precision is getting too large, something might be ood
          break
        end
        set_precision!(Balls, prec)
        local r
        try
          r = roots(CC, minimal_polynomial(g))
        catch e
          if e isa ErrorException && startswith(e.msg, "unable")
            prec *= 2
            continue
          end
          rethrow(e)
        end
        d = length(r)
        @assert is_pairwise(!overlaps, r)
        rabs = abs.(r)
        sort!(r; by = abs, rev = true)
        if all(i -> rabs[1] > rabs[i], 2:length(rabs)) && all(i -> rabs[i] > rabs[end], 1:length(rabs)-1)
          return r
        end
        prec = 2 * prec
      end
    end
    # have to do it precisely
    rr = reduce(vcat, [[(r, e) for r in roots(algebraic_closure(QQ), h)] for (h, e) in factor_squarefree(characteristic_polynomial(g))])
    d = nrows(g)
    rrabs = (x -> (abs(x[1]), x[2])).(rr)
    p = sortperm(rrabs; rev = true, by = x -> x[1] )
    rrabs = rrabs[p]
    if !((rrabs[1][2] == 1) && (rrabs[1][1] > rrabs[2][1]) && (rrabs[end-1] > rrabs[end]) && (rrabs[end][2] == 1))
      return false
    end
    rr = rr[p]
    r = CC.(rr)
    rabs = abs.(r)
    @assert all(i -> rabs[1] > rabs[i], 2:length(rabs)) && all(i -> rabs[i] > rabs[end], 1:length(rabs)-1)
    return r
  finally
    set_precision!(Balls, oldprec)
  end
end

function l2norm(vec::Vector{T}) where {T <: Union{RealFieldElem, ComplexFieldElem}}
  d = sum(abs(vec[i])^2 for i in 1:length(vec))
  if !is_nonnegative(d)
    # throw an error indicating that we have not enough precision to determine
    # the norm
    throw(LowPrecisionError())
  end
  return sqrt(d)
end

_dot(x, y) = abs(sum(x[i]*conj(y[i]) for i in 1:length(x)))

Hecke.conj(x::RealFieldElem) = x

# distance between vec and the hyperplance with normal vector normvec
function dist_vector_normal_vector(vec::Vector, normvec::Vector)
  @assert length(normvec) == length(vec)
  ss = abs(_dot(vec, normvec))
  return ss/(l2norm(vec) * l2norm(normvec))
end

# A*c = 0; for real c this is also the Hermitian normal
function normal_vector(A::MatElem)
  # the rows give the basis
  n = nrows(A)
  @assert n == ncols(A) - 1
  v = kernel(A; side = :right)
  @assert ncols(v) == 1
  return v[:, 1]
end

function _normal_vector_via_inv(A::MatElem)#{ComplexFieldElem})
  n = nrows(A)
  try
    B = A[:, 1:n]
    v = inv(B) * A[:, n+1]
    return true, push!(v, -one(base_ring(A)))
  catch e
    return false, elem_type(base_ring(A))[]
  end
end
  


acb_to_cc(e, x) = begin
  z = complex_field()()
  @ccall Nemo.libflint.acb_set(z::Ref{ComplexFieldElem}, e(x, precision(Balls))::Ref{AcbFieldElem})::Cvoid
  return z
end

_eigenvalue_field(::QQField, lambda::QQBarFieldElem) = QQ[lambda]

function _eigenvalue_field(F::EmbeddedAbsSimpleNumField, lambda::QQBarFieldElem)
  Qb = parent(lambda)
  a = Qb(F(gen(number_field(F))))
  return QQ[[a, lambda]]
end

_embed(::QQField, k::AbsSimpleNumField, ktoQQbar) = k

function _embed(E::EmbeddedAbsSimpleNumField, k::AbsSimpleNumField, ktoQQbar)
  K = number_field(E)
  Qb = codomain(ktoQQbar)
  # keep the embedding of the coefficient field
  e = hom(K, k, ktoQQbar\Qb(E(gen(K))))
  return x -> e(data(x))
end

function _complex_embedding_from_map(K, ktoQQbar)
  a = gen(K)
  image = ktoQQbar(a)
  embs = complex_embeddings(K)
  prec = max(64, precision(Balls))
  while true
    z = AcbField(prec)(image)
    ee = [e for e in embs if overlaps(e(a, prec), z)]
    if length(ee) == 1
      return only(ee)
    end
    @assert !isempty(ee)
    prec *= 2
  end
end

# Return (v, lambda, H), where
# - v is an eigenvector of mat with largest eigenvalue
#   (the Eigenspace is 1-dimensional by assumption)
# - lambda are the eigenvalues, sorted by absolute value
# - A normal vector for the hyperspace spanned by the remaining
#   eigenspaces
function archimedean_eigenspace_data(mat)
  _require_real_archimedean_input(mat)
  # fields
  CC = complex_field()
  Qb = algebraic_closure(QQ)
  # get eigenvalue and top eigenspace over Qb
  lam = Oscar.roots(Qb, characteristic_polynomial(mat))
  _with_ball_precision(1024) do
    sort!(lam; by = x -> abs(CC(x)), rev = true)
  end
  if !all(i -> abs(CC(lam[1])) > abs(CC(lam[i])), 2:length(lam))
    @info "interesting example"
    # have to resort to complicated sorting in QQbar
    sort!(lam; by = x -> abs(x), rev = true)
  end
  return _archimedean_eigenspace_data(mat, lam)
end

# TODO: Nemo 0.54.2's _eig_simple/_eig_multiple should return v_approx, not v.
# Check ComplexMat.jl/acb_mat.jl on [2 1; 1 1] and repeated roots.

# solve over intervals with v[j] = 1
# det(h-lambda*I) = 0 gives the remaining equation
function _eigenvector_from_isolated_eigenvalue(h::QQMatrix, lambda::RealFieldElem)
  n = nrows(h)
  RR = real_field()
  a = matrix(RR, h)
  for j in sortperm([abs(h[i,i]) for i in 1:n]; rev = true)
    ind = [i for i in 1:n if i != j]
    B = a[ind, ind] - lambda * identity_matrix(RR, n-1)
    fl, Bi = is_invertible_with_inverse(B)
    fl || continue
    v = zeros(RR, n)
    v[j] = RR(1)
    v[ind] = -Bi * a[ind, j]
    return v
  end
  throw(LowPrecisionError())
end

function _archimedean_eigenspace_data(mat::QQMatrix, lam)
  # need a simple real dominant eigenvalue
  if length(lam) != nrows(mat) || !is_real(lam[1]) ||
     (length(lam) > 1 && lam[1] == lam[2])
    return invoke(_archimedean_eigenspace_data, Tuple{Any, Any}, mat, lam)
  end
  prec = max(32, precision(Balls))
  while true
    result = _with_ball_precision(prec) do
      CC = complex_field()
      lambda = real(CC(lam[1]))
      try
        u = _eigenvector_from_isolated_eigenvalue(transpose(mat), lambda)
        # the right eigenvector is normal to the other left eigenspaces
        normal = _eigenvector_from_isolated_eigenvalue(mat, lambda)
        return CC.(u), lam, CC.(normal)
      catch err
        err isa LowPrecisionError || rethrow()
        return nothing
      end
    end
    result === nothing || return result
    prec *= 2
  end
end

function _archimedean_eigenspace_data(mat, lam)
  CC = complex_field()
  # lam[1] is the largest eigenvalue
  # work in F(lam[1]) with the given embedding
  K, KtoQQbar = _eigenvalue_field(base_ring(mat), lam[1])
  lamK = KtoQQbar\(lam[1])
  # @info "" lam 
  e = _embed(base_ring(mat), K, KtoQQbar)
  es = eigenspace(map_entries(e, mat), KtoQQbar\(lam[1]))
  mu = map_coefficients(e, minpoly(mat); cached = false)
  g = divexact(mu, gen(parent(mu)) - lamK)
  Es = kernel(g(map_entries(e, mat))) # the sum of the other eigenspaces
  @assert nrows(Es) == nrows(mat) - 1

  # lam[1] alone need not distinguish the embeddings of F
  ee = _complex_embedding_from_map(K, KtoQQbar)

  # c can be chosen real for the supported embeddings
  # try interval inversion first, then exact linear algebra
  fl, _hs = _normal_vector_via_inv(acb_to_cc.(Ref(ee), Es))
  if fl
    hscc = _hs
  else
    hs = normal_vector(Es)
    hscc = acb_to_cc.(Ref(ee), hs)
  end
  # result over C
  # find the correct embedding K -> C
  return (acb_to_cc.(Ref(ee), es))[1, :], lam, hscc
end

function archimedean_eigenspace_data2(mat)
  _require_real_archimedean_input(mat)
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

# ||a||_o

_conjugatetranspose(a::QQMatrix) = transpose(a)

_conjugatetranspose(a::AbstractAlgebra.Generic.MatSpaceElem{EmbeddedAbsSimpleNumFieldElem}) = transpose(a)

function onorm(_mat::MatGroupElem)
  return onorm(matrix(_mat))
end

function onorm(_mat)
  _require_real_archimedean_input(_mat)
  mat = _conjugatetranspose(_mat) * _mat
  CC = complex_field()
  Qb = algebraic_closure(QQ)
  # get eigenvalue and top eigenspace over Qb
  lam = Oscar.roots(Qb, characteristic_polynomial(mat))
  _with_ball_precision(1024) do
    sort!(lam; by = x -> abs(CC(x)), rev = true)
  end
  if !all(i -> abs(CC(lam[1])) > abs(CC(lam[i])), 2:length(lam))
    @info "interesting example"
    # have to resort to complicated sorting in QQbar
    sort!(lam; by = x -> abs(x), rev = true)
  end
  # ||a||_o = sqrt(Lambda(a^* a))
  return sqrt(abs(CC(lam[1])))
end
