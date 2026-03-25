function _random_element(G; radius = 5)
    F = free_group(ngens(G))
    r = rand(1:radius)
    w = rand_pseudo(F; radius = r)
    return G(matrix(map_word(w, gens(G))); check = false), w
end

function _random_element_glnZ(n)
    x = GAP.Globals.RandomUnimodularMat(n)
    return matrix(ZZ, x)
end
