function _random_element(G; radius = 5)
    F = free_group(ngens(G))
    return G(matrix(map_word(rand_pseudo(F; radius), gens(G))); check = false)
end

function _random_element_glnZ(n)
    x = GAP.Globals.RandomUnimodularMat(n)
    return matrix(ZZ, x)
end
