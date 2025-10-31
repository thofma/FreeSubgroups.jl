
using Oscar
using Oscar:Nemo

# step one: find pair -- G = GL(d,ZZ) is an option here

function RandomElm(G)
  F = free_group(ngens(G))
  return matrix(map_word(rand(F), gens(G)))
end

function RandomElmGL(n)
    x = GAP.Globals.RandomUnimodularMat(n)
    return matrix(ZZ,x)
end

function IsSSBiProximal(g::ZZMatrix)
#  Qb = algebraic_closure(QQ)
#  r = eigenvalues(Qb,g)
  CC = ComplexField()
  r = eigenvalues(CC,g)
  d = size(g,1)
  if length(r) < d
      return false
  end
  sort!(r; by = abs, rev = true )
  if ((abs(r[1]) > abs(r[2])) && (abs(r[d-1]) > abs(r[d]))) 
    return true
  else
    return false
  end
end

function IsIRBiProximal(g::ZZMatrix)
  f = characteristic_polynomial(g)
  if length(factor(f)) == 1
      return IsBiProximal(g)
  else
      return false
  end
end

function FindPair(G)
    pp = []
    while true 
        g = RandomElm(G)
        if IsSSBiProximal(g) 
            push!(pp, g)
            if length(pp) == 2 
                return pp;
            end
        end
    end
end
    
function FindPairGL(n)
    pp = []
    while true 
        g = RandomElmGL(n)
        if IsSSBiProximal(g) 
            push!(pp, g)
            if length(pp) == 2 
                return pp;
            end
        end
    end
end

# step two: compute delta(x,y)

function NNorm( vec )
    return sqrt( sum( (abs(vec[i]))^2 for i in 1:length(vec)))
end

function DDist( vec1, vec2 )
   ss = abs(sum( vec1[i]*vec2[i] for i in 1:length(vec1)))
   return ss / (NNorm(vec1) * NNorm(vec2))
end

function KKernel(A)
  [inv(A[:, 1:nrows(A)]) * A[:, ncols(A)]; base_ring(A)(-1)]
end

function MaxEigenVec( mat )

  # fields
  CC = ComplexField()
  Qb = QQBar
  Qm = Qb.(mat)

  # get eigenvalue and top eigenspace over Qb
  println("    eigenvalues")
  lam = eigenvalues(Qb, Qm)
  sort!(lam; by = abs, rev = true)
  println("    top eigenspace")
  es = eigenspace(Qm, lam[1])[1, :]
  println("    complement")
  Es = vcat([eigenspace(Qm, lam[i]) for i in 2:length(lam)]...)
  println("    normal vector")
  hs = KKernel(CC.(Es))
  hs = transpose(hs)
  println("  ")

  # return result over C
  return CC.(es), CC.(lam), hs
end

function DDelta(x, y)

   println(" get eigenspaces")  
   # eigenspaces and eigenvalues
   ux, ex, hx = MaxEigenVec(x)
   uX, eX, hX = MaxEigenVec(inv(x))
   uy, ey, hy = MaxEigenVec(y)
   uY, eY, hY = MaxEigenVec(inv(y))

   println(" compute distances");
   dd = []
   push!(dd, DDist(ux, hx))
   push!(dd, DDist(uy, hy))
   push!(dd, DDist(uX, hX))
   push!(dd, DDist(uY, hY))

   push!(dd, DDist(ux, hy))
   push!(dd, DDist(ux, hY))
   push!(dd, DDist(uX, hy))
   push!(dd, DDist(uX, hY))

   push!(dd, DDist(uy, hx))
   push!(dd, DDist(uy, hX))
   push!(dd, DDist(uY, hx))
   push!(dd, DDist(uY, hX))

   dd = minimum(dd)

   if dd<0 then 
       error("delta less than 0")
   end

   if dd == 0  
       return false
   else
       return dd, ex, eX, ey, eY
   end
end

function RRatio(x)
  CC = ComplexField()
  lam = eigenvalues(CC, x)
  sort!(lam; by = abs, rev = true) 
  return abs(lam[1]), abs(lam[1]/lam[2])
end

#
# b = largest eigenvalue
# c = ratio
# d = dimension
# z = -4*log(delta)
#
function MatBound(b,c,d,z)
    v = 1/(c-sqrt(c))^2
    u = b^(d/(d-1))
    return 2*  ((d-2)*log(1+u*v) + z)/abs(log(c))
end

function BBoundByPrec(x, y, prec)

    CC = ComplexField()

    # set the precision
    set_precision!(Balls, prec)

    println("compute delta")
    d = size(x,1)
    dd, ex, eX, ey, eY = DDelta(x,y)
    z = - 4*log(dd)   # 4*log(inv(dd))

    println("compute bounds")
    pp = []
    push!(pp, MatBound( abs(ex[1]), abs(ex[1]/ex[2]), d, z) )
    push!(pp, MatBound( abs(eX[1]), abs(eX[1]/eX[2]), d, z) )
    push!(pp, MatBound( abs(ey[1]), abs(ey[1]/ey[2]), d, z) )
    push!(pp, MatBound( abs(eY[1]), abs(eY[1]/eY[2]), d, z) )

    println("evaluate result")
    pp = maximum(pp)
    cc = ceil(pp)
    if radius(pp) < 1 
        return ZZ(cc)
    else
        return false
    end
end

function BBound(x,y)
    return BBoundByPrec(x,y,64)
end

