# -*- coding: utf-8 -*-
"""
Constructing a dual pair of algebras from a table.
"""

from __future__ import absolute_import

from dual_pairs import FiniteFlatAlgebra, DualPair

from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector
from sage.rings.rational_field import QQ

def algebra_and_points_from_action(G, V, action):
    """
    This is a helper function for :func:`dual_pair_from_table`.

    EXAMPLES::

        sage: from dual_pairs.dual_pair_from_table import algebra_and_points_from_action
        sage: R.<x> = QQ[]
        sage: L.<a> = NumberField(x^3 - x^2 - 2*x + 1)
        sage: G = L.galois_group()
        sage: V = GF(2)^2
        sage: M = MatrixSpace(GF(2), 2, 2)
        sage: table = {G[0]: M.one(),
        ....:          G[1]: M([1, 1, 1, 0]),
        ....:          G[2]: M([0, 1, 1, 1])}
        sage: algebra_and_points_from_action(G, V, lambda g, v: table[g] * v)
        (
        Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^3 - x^2 - 2*x + 1 ,
        [(0, 0), (0, 1), (1, 1), (1, 0)],
        [           1            0            0            0]
        [           0            1     -a^2 + 2 -a^2 + a + 3]
        [           0            1  a^2 - a - 1       -a + 2]
        [           0            1            a          a^2]
        )
    """
    T = set()
    Vlist = V.list()
    for v in Vlist:
        v.set_immutable()
    Vlist = set(Vlist)
    while Vlist:
        v = Vlist.pop()
        T.add(v)
        for g in G:
            w = action(g, v)
            w.set_immutable()
            Vlist.discard(w)

    stabilisers = {v: G.subgroup([g for g in G if action(g, v) == v])
                   for v in T}
    coset_reps = {v: {X[0] for X in G.cosets(stabilisers[v], side='left')}
                  for v in T}

    def fixed_field(H):
        # Starting from SageMath 9.0, this is the same as
        # H.fixed_field().
        if H.order() == 1:
            # Work around <https://trac.sagemath.org/ticket/26817>.
            K = G.number_field()
            return K, K.hom(K)
        try:
            return H.fixed_field()
        except AttributeError:
            # Work around <https://trac.sagemath.org/ticket/26816>.
            return G.number_field().subfield(0)

    # fixed fields
    K = {v: fixed_field(stabilisers[v]) for v in T}

    T = sorted(T)
    X = []
    points = []
    for i, v in enumerate(T):
        for g in coset_reps[v]:
            w = action(g, v)
            w.set_immutable()
            l = []
            for j, z in enumerate(T):
                if i == j:
                    l.extend(g(K[v][1](K[v][0].gen())).powers(K[v][0].degree()))
                else:
                    l.extend([0] * K[z][0].degree())
            X.append(w)
            points.append(vector(G.number_field(), l))

    A = FiniteFlatAlgebra(QQ, [K[v][0].defining_polynomial() for v in T])
    M = matrix(points)

    return A, X, M

def dual_pair_from_table(G, V, table):
    r"""
    Return a dual pair of algebras corresponding to the given
    Galois representation.

    INPUT:

    - `G` -- Galois group of a finite Galois extension of
      :math:`\mathbf{Q}`

    - `V` -- a finite-dimensional vector space over a finite field

    - ``table`` -- a dictionary ``{g: rho(g)}`` where `g` ranges
      over `G` and ``rho`` is a group homomorphism from `G` to the
      automorphism group of `V`.

    EXAMPLES::

        sage: from dual_pairs.dual_pair_from_table import dual_pair_from_table
        sage: R.<x> = QQ[]
        sage: L.<a> = NumberField(x^3 - x^2 - 2*x + 1)
        sage: G = L.galois_group()
        sage: V = GF(2)^2
        sage: M = MatrixSpace(GF(2), 2, 2)
        sage: table = {G[0]: M.one(),
        ....:          G[1]: M([1, 1, 1, 0]),
        ....:          G[2]: M([0, 1, 1, 1])}
        sage: dual_pair_from_table(G, V, table)
        Dual pair of algebras over Rational Field
        A = Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^3 - x^2 - 2*x + 1
        B = Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^3 - x^2 - 2*x + 1
    """
    L = G.number_field()
    l = V.base_ring().characteristic()  # TODO: exponent
    A, X, M = algebra_and_points_from_action(G, V, lambda g, v: table[g] * V(v))
    try:
        z = L.zeta(l)
        H = G
        def restrict(h): return h
    except ValueError:
        # There is no root of unity of order l in L.
        from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
        R = PolynomialRing(L, 'w')
        f = R.cyclotomic_polynomial(l).factor()[0][0]
        Lz = L.extension(f, 'z')
        Lz_abs = Lz.absolute_field('b')
        iota = Lz_abs.structure()[1] * Lz.coerce_map_from(L)
        H = Lz_abs.galois_group()
        z = Lz_abs(Lz.gen())
        def restrict(h):
            a = L.gen()
            ha = h(iota(a))
            return [g for g in G if iota(g(a)) == ha][0]
        M = M.apply_map(iota)

    def cyclo_char(h):
        return [a for a in range(l) if h(z) == z**a][0]

    # compute the dual representation
    table_dual = {h: table[restrict(h)].transpose()**-1 * cyclo_char(h)
                  for h in H}

    B, Y, N = algebra_and_points_from_action(H, V, lambda h, v: table_dual[h] * V(v))

    pairing = matrix([[z**((v * w).lift()) for w in Y] for v in X])
    Phi = (M.transpose() * pairing.transpose()**-1 * N).change_ring(QQ)

    return DualPair(A, B, Phi)
