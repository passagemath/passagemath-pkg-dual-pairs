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

    def nice_model(self):
        """
        Return a nice model for ``self``.

        TESTS::

            sage: R.<x> = QQ[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(QQ, [x, x^8 - x^7 - 2*x^6 + 7*x^5 - 7*x^4 + 7*x^3 - 7*x^2 + 4*x - 1])
            sage: Phi = 1/9 * matrix([[1, 8, 1, 5, -14, 17, -74, 128, -293],
            ....:                     [8, -8, -1, -5, 14, -17, 74, -128, 293],
            ....:                     [1, -1, 10, -4, 31, -118, 151, -484, 985],
            ....:                     [5, -5, -22, 34, -151, 274, -532, 1477, -2941],
            ....:                     [-14, 14, 13, 20, 115, -130, 181, -892, 1123],
            ....:                     [17, -17, -91, 76, -418, 1054, -1438, 4948, -9409],
            ....:                     [-74, 74, 115, -118, 946, -1663, 2830, -8995, 16462],
            ....:                     [128, -128, -331, 145, -1810, 3877, -5368, 19327, -34516],
            ....:                     [-293, 293, 832, -727, 5002, -10354, 15985, -52408, 97765]])
            sage: D = DualPair(A, Phi)
            sage: D.ramified_primes()
            {3, 7, 11}
            sage: D.nice_model().ramified_primes()
            {3, 11}
        """
        from .dual_pair import DualPair
        A, P = self.algebra1().nice_model()
        B, Q = self.algebra2().nice_model()
        Phi = ~P * self.phi() * ~Q.transpose()
        return DualPair(A, B, Phi)

    def lmfdb_data(self):
        """
        Return ``self`` in LMFDB format.

        TESTS::

            sage: R.<x> = QQ[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.lmfdb_data()
            [[[0, 1], [0, 1], [17, 0, 1]],
             [[0, 1], [0, 1], [17, 0, 1]],
             [4, [[1, 1, 2, 0], [1, 1, -2, 0], [2, -2, 0, 0], [0, 0, 0, -68]]]]
        """
        A = self.algebra1()
        B = self.algebra2()
        Phi = ~A._basis_matrix() * self.phi() * ~B._basis_matrix().transpose()
        den = Phi.denominator()
        return [[list(f) for f in A._polys],
                [list(g) for g in B._polys],
                [den, [list(r) for r in den * Phi]]]

    def pari_data(self):
        """
        Return ``self`` in PARI format.

        TESTS::

            sage: R.<x> = QQ[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.pari_data()
            [[x, x, x^2 + 17], [Mat(1), Mat(1), [1, 0; 0, 1]], [x, x, x^2 + 17], [Mat(1), Mat(1), [1, 0; 0, 1]], [1/4, 1/4, 1/2, 0; 1/4, 1/4, -1/2, 0; 1/2, -1/2, 0, 0; 0, 0, 0, -17]]
        """
        from sage.libs.pari import pari
        return pari([self.algebra1().pari_data(),
                     self.algebra2().pari_data(),
                     [self.phi()]]).concat()

    def torsor_class_group(self, S):
        """
        Return the group of isomorphism classes of torsors for ``self``.

        INPUT:

        - `S` -- a finite set of primes

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x^2 - 7])
            sage: B = FiniteFlatAlgebra(QQ, [x, x^2 + 21])
            sage: Phi = Matrix(QQ, [[1/3,  2/3,   0],
            ....:                   [2/3, -2/3,   0],
            ....:                   [  0,    0, 14]])
            sage: D = DualPair(A, B, Phi)
            sage: H = D.torsor_class_group([])
            sage: H
            Group of isomorphism classes of G-torsors where G is defined by
            Dual pair of algebras over Rational Field
            A = Finite flat algebra of degree 3 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x^2 - 7
            B = Finite flat algebra of degree 3 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x^2 + 21
            sage: H.group_structure()
            (Trivial Abelian group,
             [],
             <function TorsorClassGroup.group_structure.<locals>.exp at 0x...>,
             <function TorsorClassGroup.group_structure.<locals>.log at 0x...>)
        """
        from .torsor_class_group import TorsorClassGroup
        return TorsorClassGroup(self, S)
