t = 15
m1 = matrix(QQ, 3, 3, [0, 0, -1//t,  0, -t, -1//t+t,  -1, 0, -1//t+1])
m2 = matrix(QQ, 3, 3, [-t, t, 0,     0,  1, 0,          0, 1//t, -1//t])
t = 15
m1 = matrix(QQ, 3, 3, [0, 0, -1//t,  0, -t, -1//t+t,  -1, 0, -1//t+1])
m2 = matrix(QQ, 3, 3, [-t, t, 0,     0,  1, 0,          0, 1//t, -1//t])

G = matrix_group(m1, m2)

g1 = gen(G, 1)
g2 = gen(G, 2)
r1 = verify_free_pair_cones(G, g1, g2, 5)
@test r1 == true
