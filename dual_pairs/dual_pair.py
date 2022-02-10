# -*- coding: utf-8 -*-
"""
Dual pairs of algebras, representing commutative finite flat group
schemes.
"""

from __future__ import absolute_import

from sage.matrix.all import Matrix
from sage.misc.all import cached_method
from sage.rings.all import QQ, ZZ
from sage.structure.category_object import CategoryObject
from sage.structure.factory import UniqueFactory


def _dlog_fun(L, n):
    """
    Return a discrete logarithm function for the group of :math:`n`-th
    roots of unity in :math:`L`.

    EXAMPLES::

        sage: from dual_pairs.dual_pair import _dlog_fun
        sage: _dlog_fun(Qp(3), 4)
        <function _dlog_fun.<locals>.<lambda> at 0x...>
    """
    from .group_structure import mod1
    try:
        twopii = 2 * L.pi() * L(-1).sqrt()
        return lambda x: mod1(((x.log()/twopii).real() * n).round() / n)
    except AttributeError:
        pass
    from sage.rings.padics.generic_nodes import (pAdicFieldGeneric,
                                                 pAdicRingGeneric)
    if isinstance(L, (pAdicFieldGeneric, pAdicRingGeneric)):
        zeta, m = L.primitive_root_of_unity(n, order=True)
    else:
        try:
            zeta, m = L.zeta(n), n
        except ValueError:
            m = L.zeta_order().gcd(n)
            zeta = L.zeta(m)
    zeta_pow = zeta.powers(m)
    return lambda x: mod1(zeta_pow.index(x) / m)


class DualPair_class(CategoryObject):
    """
    A dual pair of finite flat algebras.

    EXAMPLES::

        sage: R.<x> = QQ[]
        sage: from dual_pairs import FiniteFlatAlgebra, DualPair
        sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
        sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
        ....:                   [1/4,  1/4, -1/2,   0],
        ....:                   [1/2, -1/2,    0,   0],
        ....:                   [  0,    0,    0, -17]])
        sage: D = DualPair(A, Phi)
        sage: D
        Dual pair of algebras over Rational Field
        A = Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x
        Number Field in a2 with defining polynomial x^2 + 17
        B = Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x
        Number Field in a2 with defining polynomial x^2 + 17
        sage: D.category()
        Category of objects
    """

    def __init__(self, alg1, alg2, phi):
        """
        Initialise a dual pair of finite flat algebras.

        This is not meant to be called directly; use
        :class:`DualPairFactory` instead.

        TESTS::

            sage: R.<x> = QQ[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: TestSuite(D).run()
        """
        self._algebra1 = alg1
        self._algebra2 = alg2
        self._phi = phi
        super(DualPair_class, self).__init__(base=alg1.base_ring())

    def _repr_(self):
        """
        Return a string representation of ``self``.

        TESTS::

            sage: K.<a> = FunctionField(QQ)
            sage: R.<x> = K[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(K, [x, x^2 - a])
            sage: B = FiniteFlatAlgebra(K, [x, x^2 + 3*a])
            sage: Phi = Matrix(K, [[1/3,  2/3,   0],
            ....:                  [2/3, -2/3,   0],
            ....:                  [  0,    0, 2*a]])
            sage: D = DualPair(A, B, Phi)
            sage: D
            Dual pair of algebras over Rational function field in a over Rational Field
            A = Finite flat algebra of degree 3 over Rational function field in a over Rational Field, product of:
            Function field in a0 defined by a0
            Function field in a1 defined by a1^2 - a
            B = Finite flat algebra of degree 3 over Rational function field in a over Rational Field, product of:
            Function field in a0 defined by a0
            Function field in a1 defined by a1^2 + 3*a
        """
        return ('Dual pair of algebras over %s\nA = %s\nB = %s'
                % (self.base_ring(), self.algebra1(), self.algebra2()))

    def algebra1(self):
        """
        Return the algebra `A` attached to ``self``.

        TESTS::

            sage: K.<a> = FunctionField(QQ)
            sage: R.<x> = K[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(K, [x, x^2 - a])
            sage: B = FiniteFlatAlgebra(K, [x, x^2 + 3*a])
            sage: Phi = Matrix(K, [[1/3,  2/3,   0],
            ....:                  [2/3, -2/3,   0],
            ....:                  [  0,    0, 2*a]])
            sage: D = DualPair(A, B, Phi)
            sage: D.algebra1()
            Finite flat algebra of degree 3 over Rational function field in a over Rational Field, product of:
            Function field in a0 defined by a0
            Function field in a1 defined by a1^2 - a
        """
        return self._algebra1

    def algebra2(self):
        """
        Return the algebra `B` attached to ``self``.

        TESTS::

            sage: K.<a> = FunctionField(QQ)
            sage: R.<x> = K[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(K, [x, x^2 - a])
            sage: B = FiniteFlatAlgebra(K, [x, x^2 + 3*a])
            sage: Phi = Matrix(K, [[1/3,  2/3,   0],
            ....:                  [2/3, -2/3,   0],
            ....:                  [  0,    0, 2*a]])
            sage: D = DualPair(A, B, Phi)
            sage: D.algebra2()
            Finite flat algebra of degree 3 over Rational function field in a over Rational Field, product of:
            Function field in a0 defined by a0
            Function field in a1 defined by a1^2 + 3*a
        """
        return self._algebra2

    def phi(self):
        """
        Return the pairing matrix attached to ``self``.

        TESTS::

            sage: K.<a> = FunctionField(QQ)
            sage: R.<x> = K[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(K, [x, x^2 - a])
            sage: B = FiniteFlatAlgebra(K, [x, x^2 + 3*a])
            sage: Phi = Matrix(K, [[1/3,  2/3,   0],
            ....:                  [2/3, -2/3,   0],
            ....:                  [  0,    0, 2*a]])
            sage: D = DualPair(A, B, Phi)
            sage: D.phi() == Phi
            True
        """
        return self._phi

    @cached_method
    def theta(self, R=None):
        r"""
        Return the canonical root of unity attached to ``self``.

        INPUT:

        - `R` -- an extension of the base ring of ``self``
          (default: the base ring itself)

        OUTPUT:

        The canonical root of unity :math:`\theta \in A_R\otimes_R B_R`,
        where `A` and `B` are the two algebras defining ``self``.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.theta()
            [    1     1     1     0]
            [    1     1    -1     0]
            [    1    -1     0     0]
            [    0     0     0 -1/17]

        .. NOTE::

            Base extension of `theta` to a given ring `R` can be quite
            slow, for example when `R` is a ramified p-adic field.  We
            therefore cache the result for any `R`.
        """
        theta = self.phi().transpose().inverse()
        return theta if R is None else theta.base_extend(R)

    def degree(self):
        """
        Return the degree of ``self``.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.degree()
            4
        """
        return self.algebra1().degree()

    def unit1(self):
        """
        Return the unit element of the algebra `A` as an element of the
        underlying module.

        EXAMPLES::

            sage: K.<a> = FunctionField(QQ)
            sage: R.<x> = K[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(K, [x, x^2 - a])
            sage: B = FiniteFlatAlgebra(K, [x, x^2 + 3*a])
            sage: Phi = Matrix(K, [[1/3,  2/3,   0],
            ....:                  [2/3, -2/3,   0],
            ....:                  [  0,    0, 2*a]])
            sage: D = DualPair(A, B, Phi)
            sage: D.unit1()
            (1, 1, 0)
        """
        return self.algebra1().one().module_element()

    def unit2(self):
        """
        Return the unit element of the algebra `B` as an element of the
        underlying module.

        EXAMPLES::

            sage: K.<a> = FunctionField(QQ)
            sage: R.<x> = K[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(K, [x, x^2 - a])
            sage: B = FiniteFlatAlgebra(K, [x, x^2 + 3*a])
            sage: Phi = Matrix(K, [[1/3,  2/3,   0],
            ....:                  [2/3, -2/3,   0],
            ....:                  [  0,    0, 2*a]])
            sage: D = DualPair(A, B, Phi)
            sage: D.unit2()
            (1, 1, 0)
        """
        return self.algebra2().one().module_element()

    @cached_method
    def counit1(self):
        """
        Return the vector of coefficients of the counit of the algebra `A`
        as an element of the dual of the underlying module.

        EXAMPLES::

            sage: K.<a> = FunctionField(QQ)
            sage: R.<x> = K[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(K, [x, x^2 - a])
            sage: B = FiniteFlatAlgebra(K, [x, x^2 + 3*a])
            sage: Phi = Matrix(K, [[1/3,  2/3,   0],
            ....:                  [2/3, -2/3,   0],
            ....:                  [  0,    0, 2*a]])
            sage: D = DualPair(A, B, Phi)
            sage: D.counit1()
            (1, 0, 0)
        """
        return self.phi() * self.unit2()

    @cached_method
    def counit2(self):
        """
        Return the vector of coefficients of the counit of the algebra `B`
        as an element of the dual of the underlying module.

        EXAMPLES::

            sage: K.<a> = FunctionField(QQ)
            sage: R.<x> = K[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(K, [x, x^2 - a])
            sage: B = FiniteFlatAlgebra(K, [x, x^2 + 3*a])
            sage: Phi = Matrix(K, [[1/3,  2/3,   0],
            ....:                  [2/3, -2/3,   0],
            ....:                  [  0,    0, 2*a]])
            sage: D = DualPair(A, B, Phi)
            sage: D.counit2()
            (1, 0, 0)
        """
        return self.unit1() * self.phi()

    def is_isomorphic(self, other):
        """
        Return ``True`` if ``self`` is isomorphic to ``other``.
        """
        raise NotImplementedError

    def change_ring(self, R):
        """
        Return a copy of ``self`` base-changed to `R`.

        EXAMPLES::

            sage: from dual_pairs import DualPair
            sage: R.<t> = ZZ[]
            sage: D = DualPair(ZZ, [[t, t]], [[1, 1], [1, -1]])
            sage: D
            Dual pair of algebras over Integer Ring
            A = Finite flat algebra of degree 2 over Integer Ring, product of:
            Order in Number Field in a0 with defining polynomial t
            Order in Number Field in a1 with defining polynomial t
            B = Finite flat algebra of degree 2 over Integer Ring, product of:
            Order in Number Field in a0 with defining polynomial t
            Order in Number Field in a1 with defining polynomial t
            sage: D.change_ring(GF(7))
            Dual pair of algebras over Finite Field of size 7
            A = Finite flat algebra of degree 2 over Finite Field of size 7, product of:
            Finite Field of size 7
            Finite Field of size 7
            B = Finite flat algebra of degree 2 over Finite Field of size 7, product of:
            Finite Field of size 7
            Finite Field of size 7
        """
        return DualPair(self.algebra1().change_ring(R), self.algebra2().change_ring(R), self.phi())

    def dual(self):
        """
        Return the Cartier dual of ``self``.

        EXAMPLES::

            sage: K.<a> = FunctionField(QQ)
            sage: R.<x> = K[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(K, [x, x^2 - a])
            sage: B = FiniteFlatAlgebra(K, [x, x^2 + 3*a])
            sage: Phi = Matrix(K, [[1/3,  2/3,   0],
            ....:                  [2/3, -2/3,   0],
            ....:                  [  0,    0, 2*a]])
            sage: D = DualPair(A, B, Phi)
            sage: D.dual()
            Dual pair of algebras over Rational function field in a over Rational Field
            A = Finite flat algebra of degree 3 over Rational function field in a over Rational Field, product of:
            Function field in a0 defined by a0
            Function field in a1 defined by a1^2 + 3*a
            B = Finite flat algebra of degree 3 over Rational function field in a over Rational Field, product of:
            Function field in a0 defined by a0
            Function field in a1 defined by a1^2 - a
        """
        return DualPair(self.algebra2(), self.algebra1(), self.phi().transpose())

    def points(self, R):
        """
        Return the group of points of ``self`` over `R`.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.points(QQ)
            [(1, 0, 0, 0), (0, 1, 0, 0)]
            sage: L.<a> = D.splitting_field()
            sage: L
            Number Field in a with defining polynomial x^2 + 17
            sage: D.points(L)
            [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, a), (0, 0, 1, -a)]
        """
        return self.algebra1().morphisms_to_ring(R)

    def dual_points(self, R):
        """
        Return the group of points of the dual of ``self`` over `R`.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: L.<a> = D.splitting_field()
            sage: L
            Number Field in a with defining polynomial x^2 + 17
            sage: D.dual_points(L)
            [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, a), (0, 0, 1, -a)]
        """
        return self.algebra2().morphisms_to_ring(R)

    def splitting_field_polynomial(self):
        r"""
        Return a defining polynomial for the splitting field of ``self``.

        .. TODO:

            This currently only works over :math:`\mathbf{Q}`.

        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: F = GF(19)
            sage: R.<x> = F[]
            sage: A = FiniteFlatAlgebra(F, [x, x, x^2 + 17])
            sage: Phi = Matrix(F, [[1/4,  1/4,  1/2,   0],
            ....:                  [1/4,  1/4, -1/2,   0],
            ....:                  [1/2, -1/2,    0,   0],
            ....:                  [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.splitting_field_polynomial()
            Traceback (most recent call last):
            ...
            PariError: incorrect type in nfsplitting [not in Z[X]] (t_POL)
        """
        f = self.algebra1().splitting_field_polynomial()
        x = f.variable_name()
        g = self.algebra2().splitting_field_polynomial()
        g = g.change_variable_name(x)
        if g == f:
            return f
        raise NotImplementedError

    @cached_method
    def splitting_field(self, names):
        r"""
        Return a splitting field for ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: F = GF(23)
            sage: R.<x> = F[]
            sage: A = FiniteFlatAlgebra(F, [x, x^2 - 7])
            sage: B = FiniteFlatAlgebra(F, [x, x^2 + 21])
            sage: Phi = Matrix(F, [[1/3,  2/3,   0],
            ....:                  [2/3, -2/3,   0],
            ....:                  [  0,    0, 14]])
            sage: D = DualPair(A, B, Phi)
            sage: D.splitting_field('a')
            Finite Field in a of size 23^2

        .. TODO:

            This is only implemented in general over
            :math:`\mathbf{Q}` and over finite fields.
        """
        R = self.base_ring()
        if not R.is_field():
            raise NotImplementedError
        if R.is_finite():
            d1 = self.algebra1().splitting_field('w1').degree()
            d2 = self.algebra2().splitting_field('w2').degree()
            return R.extension(d1.lcm(d2), names=names)
        else:
            from sage.categories.pushout import pushout
            return pushout(self.algebra1().splitting_field(names),
                           self.algebra2().splitting_field(names))

    @cached_method
    def group_structure(self, L):
        """
        Return the structure of the group of `L`-points of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: M, E, P, Q, basis1, basis2, zeta, dlog = D.group_structure(ComplexField())
            sage: M
            Additive abelian group isomorphic to Z/2 + Z/2
            sage: E
            [  0   0   0   0]
            [  0 1/2   0 1/2]
            [  0   0 1/2 1/2]
            [  0 1/2 1/2   0]
            sage: P
            [   1.00000000000000   0.000000000000000   0.000000000000000   0.000000000000000]
            [  0.000000000000000   0.000000000000000    1.00000000000000 -4.12310562561766*I]
            [  0.000000000000000    1.00000000000000   0.000000000000000   0.000000000000000]
            [  0.000000000000000   0.000000000000000    1.00000000000000  4.12310562561766*I]
            sage: Q
            [   1.00000000000000   0.000000000000000   0.000000000000000   0.000000000000000]
            [  0.000000000000000    1.00000000000000   0.000000000000000   0.000000000000000]
            [  0.000000000000000   0.000000000000000    1.00000000000000 -4.12310562561766*I]
            [  0.000000000000000   0.000000000000000    1.00000000000000  4.12310562561766*I]
            sage: basis1
            ((0.000000000000000, 1.00000000000000, 0.000000000000000, 0.000000000000000),
             (0.000000000000000, 0.000000000000000, 1.00000000000000, -4.12310562561766*I))
            sage: basis2
            ((0.000000000000000, 0.000000000000000, 1.00000000000000, -4.12310562561766*I),
             (0.000000000000000, 1.00000000000000, 0.000000000000000, 0.000000000000000))
            sage: zeta
            (-1.00000000000000, -1.00000000000000)
            sage: dlog
            <function _dlog_fun.<locals>.<lambda> at 0x...>

        A more complicated example::

            sage: from dual_pairs.dual_pair_import import dual_pair_import
            sage: D = dual_pair_import('example_data/GL2_mod_7.gp')
            sage: D.group_structure(ComplexField(200))[0]
            Additive abelian group isomorphic to Z/7 + Z/7
        """
        from .group_structure import find_group_structure
        P = self.algebra1().morphisms_to_ring(L, as_matrix=True)
        Q = self.algebra2().morphisms_to_ring(L, as_matrix=True)
        T = P * self.theta(L) * Q.transpose()
        dlog = _dlog_fun(L, self.degree())
        M, E, p, q = find_group_structure(T.apply_map(dlog, QQ))
        P.permute_rows(p)
        Q.permute_rows(q)
        elements = list(M)
        gens_indices = [elements.index(g) for g in M.gens()]
        basis1 = tuple(P.row(i) for i in gens_indices)
        basis2 = tuple(Q.row(i) for i in gens_indices)
        zeta = tuple(T[(~p)(i + 1) - 1, (~q)(i + 1) - 1] for i in gens_indices)
        return (M, E, P, Q, basis1, basis2, zeta, dlog)

    def group_structure_algebraic_closure(self):
        """
        Return the group of points of ``self`` over an algebraic closure.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: F = GF(23)
            sage: R.<x> = F[]
            sage: A = FiniteFlatAlgebra(F, [x, x, x^2 + 17])
            sage: Phi = Matrix(F, [[1/4,  1/4,  1/2,   0],
            ....:                  [1/4,  1/4, -1/2,   0],
            ....:                  [1/2, -1/2,    0,   0],
            ....:                  [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.group_structure_algebraic_closure()[0]
            Additive abelian group isomorphic to Z/2 + Z/2
        """
        return self.group_structure(self.splitting_field('w'))

    def pairing(self, P, Q):
        """
        Return the image of (P, Q) under the Cartier duality pairing.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: L.<a> = D.splitting_field()
            sage: points = D.points(L)
            sage: Matrix([[D.pairing(S, T) for S in points] for T in points])
            [ 1  1  1  1]
            [ 1  1 -1 -1]
            [ 1 -1  1 -1]
            [ 1 -1 -1  1]
        """
        R = P.base_ring()
        if Q.base_ring() is not R:
            raise ValueError("points have different base rings")
        return P * self.theta(R) * Q

    def add(self, P, Q):
        """
        Return the sum of `P` and `Q` under the group operation of
        ``self``.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: L.<a> = D.splitting_field()
            sage: O, P, Q, R = D.points(L)
            sage: D.add(P, Q) == R
            True

        """
        R = P.base_ring()
        if Q.base_ring() is not R:
            raise ValueError("points have different base rings")
        B = self.algebra2().change_ring(R)
        theta = self.theta(R)
        S = B(P * theta) * B(Q * theta)
        return self.phi() * S.module_element()

    def multiplication_by_m(self, m):
        """
        Return the multiplication-by-`m` map on ``self``.
        """
        raise NotImplementedError

    def trivial_torsor(self):
        """
        Return a trivial torsor under ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.trivial_torsor()
            Torsor for Dual pair of algebras over Rational Field
            A = Finite flat algebra of degree 4 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
            Number Field in a2 with defining polynomial x^2 + 17
            B = Finite flat algebra of degree 4 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
            Number Field in a2 with defining polynomial x^2 + 17
            T = Finite flat algebra of degree 4 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
            Number Field in a2 with defining polynomial x^2 + 17
        """
        from .torsor_pair import TorsorPair
        from .finite_flat_algebra_module import FiniteFlatAlgebraModule
        T = self.algebra1()
        U = FiniteFlatAlgebraModule(self.algebra2())
        Psi = self.phi()
        return TorsorPair(self, T, U, Psi)

    @cached_method
    def _aut_matrix_helper(self, L, basis):
        """
        Helper function for :meth:`automorphism_matrix`.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: L.<a> = QuadraticField(-17)
            sage: _, P, _, Q = D.points(L)
            sage: D._aut_matrix_helper(L, (P, Q))
            [1/2 1/2]
            [  0 1/2]
        """
        _, _, _, _, _, basis2, _, dlog = self.group_structure(L)
        return Matrix(QQ, [[dlog(self.pairing(P, Q)) for P in basis]
                           for Q in basis2])

    def automorphism_matrix(self, aut, basis=None):
        """
        Return the matrix of the automorphism ``aut``.

        INPUT:

        - ``aut`` -- an automorphism of `L` over `K`, where `K` is the
          base field of ``self`` and `L` is an extension of `K`

        - ``basis`` -- basis of the group of `L`-points of ``self``
          (default: choose some basis)

        OUTPUT:

        The matrix of the left action of ``aut`` on the group of
        `L`-points of ``self``.

        .. NOTE::

            Beware that this returns the matrix of a left action,
            although matrices in Sage act from the right by default.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<t> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [t, t^3 - t + 1])
            sage: phi = 1/4*Matrix([[1,  3, 0,  2],
            ....:                   [3, -3, 0, -2],
            ....:                   [0,  0, 4, -6],
            ....:                   [2, -2, -6, 0]])
            sage: D = DualPair(A, phi)
            sage: L.<z> = NumberField(x^6 + 7*x^4 + 18*x^2 + 23)
            sage: aut = L.hom([1/14*(z^5 + z^4 + 8*z^3 + z^2 + 26*z - 2)])
            sage: D.automorphism_matrix(aut)
            [1 1]
            [1 0]

        The representation is a group homomorphism::

            sage: rho = D.automorphism_matrix
            sage: G = L.automorphisms()
            sage: all(rho(s * t) == rho(s) * rho(t) for s in G for t in G)
            True
        """
        from sage.rings.all import IntegerModRing
        L = aut.domain()
        M, _, _, _, basis1, basis2, _, dlog = self.group_structure(L)
        if basis is None:
            basis = basis1
        d = M.exponent()
        T = self._aut_matrix_helper(L, basis)
        basis = tuple(P.apply_map(aut) for P in basis)
        U = Matrix(QQ, [[dlog(self.pairing(P, Q))
                         for P in basis] for Q in basis2])
        return T.solve_left(U).change_ring(IntegerModRing(d))

    @cached_method
    def frobenius_matrix(self, q=None):
        """
        Return the matrix of the `q`-power Frobenius automorphism on
        ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<t> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [t, t^3 - t + 1])
            sage: phi = 1/4*Matrix([[1,  3, 0,  2],
            ....:                   [3, -3, 0, -2],
            ....:                   [0,  0, 4, -6],
            ....:                   [2, -2, -6, 0]])
            sage: D = DualPair(A, phi)
            sage: {p: D.frobenius_matrix(p) for p in {3, 5, 7, 11, 13}}
            {3: [0 1]
                [1 1],
             5: [1 1]
                [0 1],
             7: [1 1]
                [0 1],
             11: [1 1]
                 [0 1],
             13: [0 1]
                 [1 1]}
            sage: D.frobenius_matrix(2)
            Traceback (most recent call last):
            ...
            ZeroDivisionError: inverse of Mod(0, 2) does not exist
            sage: D.frobenius_matrix(23)
            Traceback (most recent call last):
            ...
            ZeroDivisionError: input matrix must be nonsingular
        """
        K = self.base_ring()
        if K.is_finite():
            p = K.characteristic()
            L = self.splitting_field('w')
            if q is None:
                q = K.cardinality()
            q = ZZ(q)
            if not q.is_power_of(p):
                raise ValueError('%s is not a power of %s' % (q, p))
            F = L.frobenius_endomorphism(q.log(p))
            return self.automorphism_matrix(F)
        else:
            from sage.rings.all import FiniteField
            if q is None:
                raise ValueError("should pass a prime power to Frob")
            return self.change_ring(FiniteField(q, 'a')).frobenius_matrix()

    def frobenius_charpoly(self, q=None):
        """
        Return the characteristic polynomial of the `q`-power Frobenius
        automorphism on ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<t> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [t, t^3 - t + 1])
            sage: phi = 1/4*Matrix([[1,  3, 0,  2],
            ....:                   [3, -3, 0, -2],
            ....:                   [0,  0, 4, -6],
            ....:                   [2, -2, -6, 0]])
            sage: D = DualPair(A, phi)
            sage: {p: D.frobenius_charpoly(p) for p in {3, 5, 7, 11, 13}}
            {3: x^2 + x + 1,
             5: x^2 + 1,
             7: x^2 + 1,
             11: x^2 + 1,
             13: x^2 + x + 1}

        A more complicated example::

            sage: from dual_pairs.dual_pair_import import dual_pair_import
            sage: D = dual_pair_import('example_data/GL2_mod_5.gp')
            sage: {p: D.frobenius_charpoly(p) for p in {3, 7, 11, 13, 17, 19, 23}}
            {3: x^2 + 4*x + 2,
             7: x^2 + x + 3,
             11: x^2 + 4*x + 1,
             13: x^2 + 3*x + 2,
             17: x^2 + 3,
             19: x^2 + x + 4,
             23: x^2 + x + 2}
        """
        return self.frobenius_matrix(q).charpoly()

    def representation_table(self, L=None, basis=None):
        """
        Return the representation table of ``self``.

        EXAMPLES::

            sage: R.<x> = QQ[]
            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.representation_table()
            {Ring endomorphism of Number Field in z with defining polynomial x^2 + 17
             Defn: z |--> -z: [1 1]
                              [0 1],
             Ring endomorphism of Number Field in z with defining polynomial x^2 + 17
             Defn: z |--> z: [1 0]
                             [0 1]}

            sage: R.<t> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [t, t^3 - t + 1])
            sage: phi = 1/4*Matrix([[1,  3, 0,  2],
            ....:                   [3, -3, 0, -2],
            ....:                   [0,  0, 4, -6],
            ....:                   [2, -2, -6, 0]])
            sage: D = DualPair(A, phi)
            sage: L.<z> = NumberField(x^6 + 7*x^4 + 18*x^2 + 23)
            sage: table = D.representation_table(L)
            sage: {f(z): m for f, m in table.items()}
            {z: [1 0]
                [0 1],
             -z: [1 1]
                 [0 1],
             -1/14*z^5 - 1/14*z^4 - 4/7*z^3 - 1/14*z^2 - 13/7*z + 1/7: [1 0]
                                                                       [1 1],
             -1/14*z^5 + 1/14*z^4 - 4/7*z^3 + 1/14*z^2 - 13/7*z - 1/7: [0 1]
                                                                       [1 0],
             1/14*z^5 - 1/14*z^4 + 4/7*z^3 - 1/14*z^2 + 13/7*z + 1/7: [0 1]
                                                                      [1 1],
             1/14*z^5 + 1/14*z^4 + 4/7*z^3 + 1/14*z^2 + 13/7*z - 1/7: [1 1]
                                                                      [1 0]}
        """
        if L is None:
            L = self.splitting_field('z')
        G = L.automorphisms()
        return {g: self.automorphism_matrix(g, basis) for g in G}

    def conductor_exponent(self, p):
        """
        Return the exponent of the local Artin conductor of ``self`` at `p`.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<t> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [t, t^3 - t + 1])
            sage: phi = 1/4*Matrix([[1,  3, 0,  2],
            ....:                   [3, -3, 0, -2],
            ....:                   [0,  0, 4, -6],
            ....:                   [2, -2, -6, 0]])
            sage: D = DualPair(A, phi)
            sage: D.conductor_exponent(2)
            0
            sage: D.conductor_exponent(7)
            0
            sage: D.conductor_exponent(23)
            1
        """
        from sage.modules.all import VectorSpace
        from sage.rings.all import FiniteField, pAdicField
        from sage.rings.infinity import infinity
        from sage.rings.padics.precision_error import PrecisionError
        from .padic_roots import kummer_dedekind, integral_basis_generator, padic_aut
        # TODO: use a p-adic splitting field (not implemented in Sage)
        g = self.splitting_field_polynomial()
        prec = 20
        while True:
            Qp = pAdicField(p, prec)
            try:
                h = g.base_extend(Qp).factor()[0][0]
            except PrecisionError:
                prec *= 2
            else:
                break
        h = integral_basis_generator(h)
        L = Qp.extension(h, names='a')
        if L.ramification_index() == 1:
            return ZZ(0)
        M, _, _, _, basis, _, _, _ = self.group_structure(L)
        F = FiniteField(M.exponent())
        dim = len(M.invariants())
        roots = h.base_extend(L).roots(multiplicities=False)
        assert len(roots) == L.degree()
        assert L.gen() in roots
        indices = [(r - L.gen()).valuation() - 1 for r in roots]
        breaks = sorted(set(indices).difference({infinity}))
        assert breaks != []
        lengths = [breaks[0] + 1] + [breaks[i] - breaks[i-1]
                                     for i in range(1, len(breaks))]
        # from smaller to larger subgroups of G_0
        breaks.reverse()
        lengths.reverse()
        V = VectorSpace(F, dim)
        f = ZZ(0)
        for i, l in zip(breaks, lengths):
            # compute order of G_i
            gi = len([k for k in indices if k >= i])
            # compute elements in G_i \ G_{i+1}
            Ri = [r for j, r in enumerate(roots) if indices[j] == i]
            if V.dimension() > 0:
                # compute G_i-invariants
                for g in Ri:
                    aut_g = padic_aut(L, g)
                    m = self.automorphism_matrix(aut_g, basis)
                    V = V.intersection((m.change_ring(F) - 1).kernel())
                    if V.dimension() == 0:
                        break
            f += l * gi * (dim - V.dimension())
        assert f % L.degree() == 0
        return f // L.degree()

    def artin_conductor(self):
        """
        Return the prime-to-`l` part of the Artin conductor of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<t> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [t, t^3 - t + 1])
            sage: phi = 1/4*Matrix([[1,  3, 0,  2],
            ....:                   [3, -3, 0, -2],
            ....:                   [0,  0, 4, -6],
            ....:                   [2, -2, -6, 0]])
            sage: D = DualPair(A, phi)
            sage: D.artin_conductor()
            23

            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.artin_conductor()
            17

            sage: D = DualPair(QQ, [[t, t^3 - 2]], [[1/4, 3/4, 0, 0], [3/4, -3/4, 0, 0], [0, 0, 0, 3], [0, 0, 3, 0]])
            sage: D.artin_conductor()
            27

            sage: D = DualPair(QQ, [[t, t^8 - 4*t^7 + 10*t^6 - 16*t^5 + 16*t^4 - 4*t^3 - 14*t^2 + 20*t - 11], [[1], [1, 3/23*t^7 - 20/23*t^6 + 45/23*t^5 - 76/23*t^4 + 59/23*t^3 + 7/23*t^2 - 99/23*t + 94/23, -1/23*t^7 - 1/23*t^6 + 8/23*t^5 - 13/23*t^4 + 34/23*t^3 - 10/23*t^2 - 13/23*t + 30/23, -4/23*t^7 - 4/23*t^6 + 9/23*t^5 - 29/23*t^4 + 44/23*t^3 - 17/23*t^2 - 29/23*t + 74/23, t - 1, 15/23*t^7 - 54/23*t^6 + 110/23*t^5 - 150/23*t^4 + 88/23*t^3 + 81/23*t^2 - 219/23*t + 148/23, -4/23*t^7 + 19/23*t^6 - 37/23*t^5 + 63/23*t^4 - 48/23*t^3 + 6/23*t^2 + 63/23*t - 41/23, 18/23*t^7 - 51/23*t^6 + 109/23*t^5 - 134/23*t^4 + 78/23*t^3 + 65/23*t^2 - 180/23*t + 81/23]]], [[1/9, 8/9, 0, -4/9, 4/9, -4/9, 4/9, 4/9, -4/9], [8/9, -8/9, 0, 4/9, -4/9, 4/9, -4/9, -4/9, 4/9], [0, 0, 0, 0, 0, 0, 0, 0, -4], [-4/9, 4/9, 0, 16/9, 20/9, 16/9, 20/9, 20/9, 16/9], [4/9, -4/9, 0, 20/9, 16/9, -16/9, 16/9, -20/9, 20/9], [-4/9, 4/9, 0, -20/9, -16/9, -20/9, 20/9, -16/9, 16/9], [4/9, -4/9, 0, 20/9, 16/9, -16/9, 16/9, 16/9, -16/9], [4/9, -4/9, 0, 20/9, -20/9, -16/9, 16/9, 16/9, 20/9], [-4/9, 4/9, 4, -20/9, 20/9, 16/9, 20/9, 20/9, -20/9]])
            sage: D.artin_conductor()  # long time (14 s)
            32
        """
        from sage.misc.all import prod
        return prod(p ** self.conductor_exponent(p)
                    for p in self.algebra1().ramified_primes()
                    if self.degree() % p != 0)

    def weight(self):
        """
        Return the Serre weight of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<t> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [t, t^3 - t + 1])
            sage: phi = 1/4*Matrix([[1,  3, 0,  2],
            ....:                   [3, -3, 0, -2],
            ....:                   [0,  0, 4, -6],
            ....:                   [2, -2, -6, 0]])
            sage: D = DualPair(A, phi)
            sage: D.weight()
            1

            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: D.weight()
            2

            sage: D = DualPair(QQ, [[t, t^3 - 2]], [[1/4, 3/4, 0, 0], [3/4, -3/4, 0, 0], [0, 0, 0, 3], [0, 0, 3, 0]])
            sage: D.weight()
            2

            sage: D = DualPair(QQ, [[t, t^8 - 4*t^7 + 10*t^6 - 16*t^5 + 16*t^4 - 4*t^3 - 14*t^2 + 20*t - 11], [[1], [1, 3/23*t^7 - 20/23*t^6 + 45/23*t^5 - 76/23*t^4 + 59/23*t^3 + 7/23*t^2 - 99/23*t + 94/23, -1/23*t^7 - 1/23*t^6 + 8/23*t^5 - 13/23*t^4 + 34/23*t^3 - 10/23*t^2 - 13/23*t + 30/23, -4/23*t^7 - 4/23*t^6 + 9/23*t^5 - 29/23*t^4 + 44/23*t^3 - 17/23*t^2 - 29/23*t + 74/23, t - 1, 15/23*t^7 - 54/23*t^6 + 110/23*t^5 - 150/23*t^4 + 88/23*t^3 + 81/23*t^2 - 219/23*t + 148/23, -4/23*t^7 + 19/23*t^6 - 37/23*t^5 + 63/23*t^4 - 48/23*t^3 + 6/23*t^2 + 63/23*t - 41/23, 18/23*t^7 - 51/23*t^6 + 109/23*t^5 - 134/23*t^4 + 78/23*t^3 + 65/23*t^2 - 180/23*t + 81/23]]], [[1/9, 8/9, 0, -4/9, 4/9, -4/9, 4/9, 4/9, -4/9], [8/9, -8/9, 0, 4/9, -4/9, 4/9, -4/9, -4/9, 4/9], [0, 0, 0, 0, 0, 0, 0, 0, -4], [-4/9, 4/9, 0, 16/9, 20/9, 16/9, 20/9, 20/9, 16/9], [4/9, -4/9, 0, 20/9, 16/9, -16/9, 16/9, -20/9, 20/9], [-4/9, 4/9, 0, -20/9, -16/9, -20/9, 20/9, -16/9, 16/9], [4/9, -4/9, 0, 20/9, 16/9, -16/9, 16/9, 16/9, -16/9], [4/9, -4/9, 0, 20/9, -20/9, -16/9, 16/9, 16/9, 20/9], [-4/9, 4/9, 4, -20/9, 20/9, 16/9, 20/9, 20/9, -20/9]])
            sage: D.weight()  # long time (14 s)
            2
        """
        from sage.arith.misc import primes
        from sage.rings.all import infinity, Mod
        from sage.rings.all import ComplexField
        L = ComplexField(800)  # TODO: adapt precision
        N = self.artin_conductor()
        M, _, _, _, basis, _, _, _ = self.group_structure(L)
        l = M.exponent()
        if not l.is_prime():
            raise ValueError("value ring of the representation must be a finite field")
        dim = len(M.invariants())
        if dim != 2:
            raise ValueError("representation must be 2-dimensional")
        for p in primes(2, infinity):
            if (p % N == 1 and p % l != 0
                and Mod(p, l).is_primitive_root()):
                try:
                    d = self.frobenius_matrix(p).determinant()
                except ZeroDivisionError:
                    continue
                k = d.log(p) + 1
                if k == 1 and l in self.algebra1().ramified_primes():
                    k = l
                return k


class DualPairFactory(UniqueFactory):
    """
    Factory for dual pairs of algebras.
    """
    def create_key(self, *data):
        """
        Return a key for the dual pair of algebras defined by the given
        data.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: DualPair.create_key(A, Phi)
            (
            Finite flat algebra of degree 4 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
            Number Field in a2 with defining polynomial x^2 + 17            ,
            Finite flat algebra of degree 4 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
            Number Field in a2 with defining polynomial x^2 + 17            ,
            [ 1/4  1/4  1/2    0]
            [ 1/4  1/4 -1/2    0]
            [ 1/2 -1/2    0    0]
            [   0    0    0  -17]
            )
        """
        from sage.matrix.all import MatrixSpace
        from .finite_flat_algebra import FiniteFlatAlgebra, FiniteFlatAlgebra_base
        if len(data) == 0:
            raise ValueError('no arguments given')
        if isinstance(data[0], FiniteFlatAlgebra_base):
            if len(data) == 2:
                alg1, phi = data
                alg2 = alg1
            else:
                alg1, alg2, phi = data
            base_ring = alg1.base_ring()
            if alg2.base_ring() is not base_ring:
                raise ValueError('inconsistent base rings')
        else:
            if len(data) == 3:
                base_ring, alg1, phi = data
                alg2 = None
            else:
                base_ring, alg1, alg2, phi = data
            alg1 = FiniteFlatAlgebra(base_ring, *alg1)
            if alg2 is None:
                alg2 = alg1
            else:
                alg2 = FiniteFlatAlgebra(base_ring, *alg2)
        n = alg1.degree()
        if alg2.degree() != n:
            raise ValueError('inconsistent degrees')
        phi = MatrixSpace(base_ring, n, n)(phi)
        return (alg1, alg2, phi)

    def create_object(self, version, key):
        """
        Return the dual pair of algebras defined by the given key.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: DualPair.create_object((8, 8), (A, A, Phi))
            Dual pair of algebras over Rational Field
            A = Finite flat algebra of degree 4 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
            Number Field in a2 with defining polynomial x^2 + 17
            B = Finite flat algebra of degree 4 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
            Number Field in a2 with defining polynomial x^2 + 17
        """
        if key[0].base_ring() is QQ:
            from dual_pairs.dual_pair_rational import DualPair_rational
            return DualPair_rational(*key)
        return DualPair_class(*key)


DualPair = DualPairFactory("dual_pairs.dual_pair.DualPair")
