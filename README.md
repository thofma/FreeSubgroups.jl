# FreeSubgroups

`FreeSubgroups` is a Julia package for finding and certifying non-abelian free
subgroups in matrix groups using the methods from

> Emmanuel Breuillard, B. Eick, D. Holt, T. Hofmann and E. A. O’Brien. *Constructing free subgroups of matrix groups*.

It is built on top of `Oscar` and combines several complementary strategies:

- rigorous archimedean bounds for biproximal pairs,
- rigorous conjugator bounds in the archimedean and p-adic settings,
- cone-based ping-pong verification,
- heuristic search via SVD and p-adic Cartan methods.

The package reexports `Oscar`, so the examples below only need
`using FreeSubgroups`.

## Setup

Install the package using the Julia package manager:

```julia
]add https://github.com/thofma/FreeSubgroups.jl
```

Then load the package with:

```julia
using FreeSubgroups
```

## Main functions

The search routines below assume that the input matrix group is not
solvable-by-finite. They are randomized, so the specific elements and words may
change from run to run.

| Function | Purpose | Return value |
| --- | --- | --- |
| `bound_biproximal(x, y)` | Certified exponent for a biproximal pair | integer `l` |
| `bound_conjugator(x, b)` | Certified exponent for `x` and `x^b` | integer `l` |
| `bound_conjugator_padic(x, b, p)` | Certified p-adic exponent for `x` and `x^b` | integer `l` |
| `verify_free_pair_cones(G, g1, g2, pow; ...)` | Cone-based ping-pong verification | `Bool` |
| `find_free_pair_biproximal(G; ...)` | Search for a certified biproximal pair | `((x, y), (wx, wy), l)` |
| `find_free_pair_conjugator(G; ...)` | Search for a certified conjugator pair | `((x, b), (wx, wb), l)` |
| `find_free_pair_conjugator_padic(G; ...)` | Search for a certified p-adic conjugator pair | `((x, b), (wx, wb), l)` |
| `find_free_pair_svd(G)` | Heuristic SVD-based search for a free pair | `((x, b), (wx, wb))` |
| `find_free_pair_cartan(G; ...)` | Heuristic p-adic Cartan search for a free pair | `((x, b), (wx, wb))` |

For the conjugator-based methods, the actual free pair is `x` and `x^b`. The
objects `wx`, `wy`, and `wb` are words in the original generators of `G`.

## Example: bounds and free-pair searches

```julia
using FreeSubgroups

A = matrix(QQ, 3, 3, [0, 0, 1//10,
					  0, -10, 99//10,
					  -1, 0, 9//10])
B = matrix(QQ, 3, 3, [-10, 10, 0,
					  0, 1, 0,
					  0, 1//10, -1//10])

fl, l0 = can_compute_biproximal_bound(A, B)
@assert fl

l = bound_biproximal(A, B)

G = matrix_group([A, B])

((x, y), (wx, wy), l_biprox) = find_free_pair_biproximal(G)
((xc, b), (wxc, wb), l_conj) = find_free_pair_conjugator(G)
((xp, bp), (wxp, wbp), l_padic) = find_free_pair_conjugator_padic(G)

((xs, bs), (wxs, wbs)) = find_free_pair_svd(G)
((xk, bk), (wxk, wbk)) = find_free_pair_cartan(G)
```

The first three search routines return an exponent `l`, such that `x^l, y^l` is a free pair. The SVD and
Cartan routines return directly a free pair.

## Example: cone verification

```julia
using FreeSubgroups

t = 15
m1 = matrix(QQ, 3, 3, [0, 0, -1//t,
					   0, -t, -1//t + t,
					   -1, 0, -1//t + 1])
m2 = matrix(QQ, 3, 3, [-t, t, 0,
					   0, 1, 0,
					   0, 1//t, -1//t])

G = matrix_group(m1, m2)
g1 = gen(G, 1)
g2 = gen(G, 2)

@assert verify_free_pair_cones(G, g1, g2, 5)
```

`verify_free_pair_cones` also accepts keyword arguments `inc`, `pow1`, and
`precision` to tune the cone radius, the power used in the eigenvector
approximation, and the working precision.

## Example: conjugator bounds

```julia
using FreeSubgroups

A, B, b = burau_representation(t = 17)
@assert B == inv(b) * A * b

l_arch = bound_conjugator(A, b)

A11, _, b11 = burau_representation(t = 11)

l_padic = bound_conjugator_padic(A11, b11, 11)
```

## Verbose output

By running

```
set_verbosity_level(:FreeSubgroups, 1)
```

verbose output is enabled.

## Utility exports

The package also exports a few helpers that are useful when building examples
or generating input groups:

- `burau_representation(; t)`
- `is_biproximal(g)`
