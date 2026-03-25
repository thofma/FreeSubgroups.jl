function burau_representation(; t)
  QQs, s = rational_function_field(QQ, :s)
  A = matrix(QQs, [0 0 s^-1; 0 -s -s^-1+s; -1 0 -s^-1 + 1]);
  B = matrix(QQs, [-s s 0; 0 1 0; 0 s^-1 -s^-1])
  return map_entries(f -> evaluate(f, t), A), map_entries(f -> evaluate(f, t), B)
end

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
