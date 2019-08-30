# -*- coding: utf-8 -*-
"""
Dual pairs of algebras over the rational numbers.
"""

from __future__ import absolute_import

from sage.misc.all import cached_method

from dual_pairs.dual_pair import DualPair_class

def lift_to_prime(a):
    """
    Return the smallest prime in the residue class `a`.

    EXAMPLES::

        sage: from dual_pairs.dual_pair_rational import lift_to_prime
        sage: [lift_to_prime(x) for x in Zmod(10) if x.is_unit()]
        [11, 3, 7, 19]
    """
    n = a.modulus()
    p = a.lift()
    while not p.is_prime():
        p += n
    return p

class DualPair_rational(DualPair_class):
    r"""
    A dual pair of algebras over the field :math:`\mathbf{Q}`.

    TESTS::

        sage: R.<x> = QQ[]
        sage: from dual_pairs import FiniteFlatAlgebra, DualPair
        sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
        sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
        ....:                   [1/4,  1/4, -1/2,   0],
        ....:                   [1/2, -1/2,    0,   0],
        ....:                   [  0,    0,    0, -17]])
        sage: D = DualPair(A, Phi)
        sage: type(D)
        <class 'dual_pairs.dual_pair_rational.DualPair_rational'>
    """

    @cached_method
    def splitting_field_polynomial(self):
        r"""
        Return a defining polynomial for the splitting field of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.splitting_field_polynomial()
            x^2 + 17
        """
        from sage.libs.pari import pari
        f = self.algebra1().splitting_field_polynomial()
        x = f.variable_name()
        g = self.algebra2().splitting_field_polynomial()
        g = g.change_variable_name(x)
        if g == f:
            return f
        comp = pari(f).polcompositum(g)
        return f.parent()(comp[len(comp) - 1])

    def splitting_field(self, names):
        r"""
        Return a splitting field for ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x^2 - 7])
            sage: B = FiniteFlatAlgebra(QQ, [x, x^2 + 21])
            sage: Phi = Matrix(QQ, [[1/3,  2/3,   0],
            ....:                   [2/3, -2/3,   0],
            ....:                   [  0,    0, 14]])
            sage: D = DualPair(A, B, Phi)
            sage: D.splitting_field('a')
            Number Field in a with defining polynomial x^4 + 28*x^2 + 784
        """
        from sage.rings.all import QQ
        return QQ.extension(self.splitting_field_polynomial(),
                            names=names)

    @cached_method
    def ramified_primes(self):
        """
        Return the set of ramified primes of ``self``.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.ramified_primes()
            {2, 17}
        """
        P = self.algebra1().ramified_primes()
        return P.union(self.degree().prime_divisors())

    def group_structure_algebraic_closure(self):
        """
        Return the group of points of ``self`` over an algebraic closure.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.group_structure_algebraic_closure()[0]
            Additive abelian group isomorphic to Z/2 + Z/2
        """
        from sage.rings.all import ComplexField
        L = ComplexField(800)  # TODO: adapt precision
        return self.group_structure(L)

    def frobenius_traces(self, B=100):
        """
        Return the traces of Frobenius elements at all unramified primes
        below `B`.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<t> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [t, t^3 - t + 1])
            sage: phi = 1/4*Matrix([[1,  3, 0,  2],
            ....:                   [3, -3, 0, -2],
            ....:                   [0,  0, 4, -6],
            ....:                   [2, -2, -6, 0]])
            sage: D = DualPair(A, phi)
            sage: D.frobenius_traces()
            [(3, 1),
             (5, 0),
             (7, 0),
             (11, 0),
             (13, 1),
             (17, 0),
             (19, 0),
             (29, 1),
             (31, 1),
             (37, 0),
             (41, 1),
             (43, 0),
             (47, 1),
             (53, 0),
             (59, 0),
             (61, 0),
             (67, 0),
             (71, 1),
             (73, 1),
             (79, 0),
             (83, 0),
             (89, 0),
             (97, 0)]

        Verify numerically that the dual pair from ``GL2_mod_3.gp``
        corresponds to the 3-torsion of the elliptic curve ``11a3``::

            sage: from dual_pairs.dual_pair_import import dual_pair_import
            sage: D = dual_pair_import('example_data/GL2_mod_3.gp')
            sage: E = EllipticCurve('11a3')
            sage: all(Mod(E.ap(p), 3) == t for p, t in D.frobenius_traces())
            True
        """
        from sage.arith.misc import primes
        P = self.ramified_primes()
        L = []
        for p in primes(B):
            if p not in P:
                L.append((p, self.frobenius_matrix(p).trace()))
        return L

    @cached_method
    def dirichlet_character(self):
        """
        Return the Dirichlet character corresponding to the determinant of
        ``self``.

        EXAMPLES::

            sage: from dual_pairs.dual_pair_import import dual_pair_import
            sage: D = dual_pair_import('example_data/D4_mod_3.gp')
            sage: chi = D.dirichlet_character(); chi
            Dirichlet character modulo 39 of conductor 39 mapping 14 |--> 2, 28 |--> 2
            sage: p = random_prime(1000)
            sage: D.dirichlet_character()(p) == D.frobenius_charpoly(p).constant_coefficient()
            True
            sage: D = dual_pair_import('example_data/GL2_mod_3.gp')
            sage: D.dirichlet_character()
            Dirichlet character modulo 3 of conductor 3 mapping 2 |--> 2
            sage: D = dual_pair_import('example_data/GL2_mod_5.gp')
            sage: D.dirichlet_character()
            Dirichlet character modulo 5 of conductor 5 mapping 2 |--> 3
        """
        from sage.modular.dirichlet import DirichletGroup
        from sage.rings.finite_rings.finite_field_constructor import FiniteField
        S = self.ramified_primes()
        # TODO: avoid computing the group structure over CC
        l = self.group_structure_algebraic_closure()[0].exponent()
        if not l.is_prime():
            raise NotImplementedError('coefficient ring must be a prime field')
        r = l - 1
        if 2 in S:
            n = 2 ** (2 + r.valuation(2)) if r % 2 == 0 else 2
        else:
            n = 1
        for p in S.difference({2}):
            n *= p ** (1 + r.valuation(p))
        G = DirichletGroup(n, FiniteField(l))
        P = [lift_to_prime(g) for g in G.unit_gens()]
        chi = G([self.frobenius_matrix(p).determinant() for p in P])
        return chi.primitive_character()
