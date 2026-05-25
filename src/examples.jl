function burau_representation(; t)
  QQs, s = rational_function_field(QQ, :s)
  A = matrix(QQs, [0 0 -s^-1; 0 -s -s^-1+s; -1 0 -s^-1 + 1]);
  B = matrix(QQs, [-s s 0; 0 1 0; 0 s^-1 -s^-1])
  b = matrix(QQ, 3, 3, [0, 0, -1, 1, 0, -1, 0, 1, -1])
  @assert B == inv(b) * A * b
  return map_entries(f -> evaluate(f, t), A), map_entries(f -> evaluate(f, t), B), b
end

#function burau_representation_new(; t)
#  QQs, s = rational_function_field(QQ, :s)
#  sigma1 = matrix(QQs, [-s 1 0; 0 1 0; 0 0 1])
#  sigma2 = matrix(QQs, [1 0 0; s -s 1; 0 0 1])
#  sigma3 = matrix(QQs, [1 0 0; 0 1 0; 0 s -s])
#  X = matrix(QQs, [-s 1 0;
#                   0 1 0;
#                   0 1 -s^-1])
#  Y = matrix(QQs, [1-s -s^-1 s^-1;
#                   1-s^2 -s^-1 0;
#                   1 -s^-1 0])
#  b = matrix(QQs, [1 0 0;
#                   s -s 1;
#                   0 0 1])
#  @assert sigma1 * inv(sigma3) == X
#  #@assert sigma2 * sigma1 * inv(sigma3) * inv(sigma2) == Y
#  @assert Y  == sigma2 * X * sigma2^-1
#  return map_entries(f -> evaluate(f, t), X),
#         map_entries(f -> evaluate(f, t), Y),
#         map_entries(f -> evaluate(f, t), b)
#end

function random_subgroup_gln(::QQField, n::Int, k::Int = 2; entry_bound = 2)
  gens = QQMatrix[]
  while length(gens) < k
    g = rand(matrix_space(QQ, n, n), -entry_bound:entry_bound)
    while !is_invertible(g)
      g = rand(matrix_space(QQ, n, n), -entry_bound:entry_bound)
    end
    push!(gens, g)
  end
  return matrix_group(gens)
end

function random_subgroup_sln(::QQField, n::Int, k::Int = 2; entry_bound = 2)
  gens = QQMatrix[]
  while length(gens) < k
    g = rand(matrix_space(QQ, n, n), -entry_bound:entry_bound)
    while !is_invertible(g)
      g = rand(matrix_space(QQ, n, n), -entry_bound:entry_bound)
    end
    d = det(g)
    g[:, 1] = 1//d * g[:, 1]
    @assert det(g) == 1
    push!(gens, g)
  end
  return matrix_group(gens)
end

function random_subgroup_gln(::ZZRing, n::Int, k::Int = 2; entry_bound = 2)
  gens = ZZMatrix[]
  while length(gens) < k
    g = _random_element_glnZ(n)
    push!(gens, g)
  end
  return matrix_group([QQ.(g) for g in gens])
end

function random_subgroup_sln(::ZZRing, n::Int, k::Int = 2; entry_bound = 2)
  gens = ZZMatrix[]
  while length(gens) < k
    g = _random_element_glnZ(n)
    g[:, 1] = inv(det(g)) * g[:, 1]
    @assert det(g) == 1
    push!(gens, g)
  end
  return matrix_group([QQ.(g) for g in gens])
end
