# -*- coding: utf-8 -*-
r"""
Torsor class groups for finite commutative group schemes.
"""

from __future__ import absolute_import

from sage.groups.group import AbelianGroup as AbelianGroupClass
from sage.matrix.constructor import Matrix
from sage.misc.cachefunc import cached_method
from sage.structure.element import MultiplicativeGroupElement


class Torsor(MultiplicativeGroupElement):

    def __init__(self, parent, T, tau):
        self._T = T
        self._tau = tau
        MultiplicativeGroupElement.__init__(self, parent)

    def _repr_(self):
        return 'Torsor defined by ({}, {})'.format(self._T, self._tau)

    def _mul_(self, other):
        H = self.parent()
        return H.element_class(H, self._T * other._T,
                               self._tau * other._tau)

    def __invert__(self):
        H = self.parent()
        return H.element_class(H, ~self._T, ~self._tau)

    def torsor_pair(self):
        """
        Return a torsor pair corresponding to this extension.

        OUTPUT:

        A torsor pair for the dual group scheme.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: H = D.torsor_class_group([])
            sage: H.gens()[0].torsor_pair()
            Torsor for Dual pair of algebras over Rational Field
            A = Finite flat algebra of degree 2 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
            B = Finite flat algebra of degree 2 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
            T = Finite flat algebra of degree 2 over Rational Field

            sage: A = FiniteFlatAlgebra(QQ, [x, x^3 - x^2 - 10*x + 8], [[1], [1, -x, -1/2*x^2 + 1/2*x + 3]])
            sage: Phi = 1/4 * Matrix([[1, 3, -1, -1], [3, -3, 1, 1], [-1, 1, 41, -21], [-1, 1, -21, 41]])
            sage: D = DualPair(A, Phi)
            sage: H = D.torsor_class_group([2])
            sage: H.one().torsor_pair().points(QQ)
            [(1, 1, 0, 0)]
            sage: [T.torsor_pair().points(QQ) for T in H.gens()]
            [[], [], [], []]
        """
        from .finite_flat_algebra import FiniteFlatAlgebra
        from .finite_flat_algebra_module import FiniteFlatAlgebraModule
        from .torsor_pair import TorsorPair

        H = self.parent()
        D = H.dual_pair()
        R = D.base_ring()
        n = D.degree()
        B = D.algebra2()
        mu = D.dual().hopf_algebra()[1]
        # self._T is currently not used (we only work over QQ)
        tau = self._tau
        # twist the multiplication tensor by tau
        M = Matrix((tau * mu(b)).module_element() for b in B.basis()).transpose()
        T = FiniteFlatAlgebra(R, [M.submatrix(i*n, 0, n, n) for i in range(n)])
        U = FiniteFlatAlgebraModule(B)
        Psi = Matrix.identity(n)
        return TorsorPair(D, T, U, Psi)


class TorsorClassGroup(AbelianGroupClass):
    """
    The group of isomorphism classes of torsors under a group scheme.

    EXAMPLES::

        sage: from dual_pairs import DualPair, FiniteFlatAlgebra
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x^3 - x^2 - 10*x + 8], [[1], [1, -x, -1/2*x^2 + 1/2*x + 3]])
        sage: Phi = 1/4 * Matrix([[1, 3, -1, -1], [3, -3, 1, 1], [-1, 1, 41, -21], [-1, 1, -21, 41]])
        sage: D = DualPair(A, Phi)
        sage: H = D.torsor_class_group([2]); H
        Group of isomorphism classes of G-torsors where G is defined by
        Dual pair of algebras over Rational Field
        A = Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^3 - x^2 - 10*x + 8
        B = Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^3 - x^2 - 10*x + 8
        sage: H.group_structure()
        (Multiplicative Abelian group isomorphic to C2 x C2 x C2 x C2,
         [Torsor defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 - 219/31*e5 + 38/31*e6 + 80/31*e7 + 38/31*e9 + 100/31*e10 + 14/31*e11 + 80/31*e13 + 14/31*e14 - 22/31*e15),
          Torsor defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 + 85/31*e5 - 52/31*e6 - 34/31*e7 - 52/31*e9 + 17/31*e10 + 13/31*e11 - 34/31*e13 + 13/31*e14 + 9/31*e15),
          Torsor defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 - 6/31*e5 + 14/31*e6 - 1/31*e7 + 14/31*e9 - 16/31*e10 - 4/31*e11 - 1/31*e13 - 4/31*e14 + 1/31*e15),
          Torsor defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 - 401/31*e5 - 102/31*e6 - 78/31*e7 - 102/31*e9 - 22/31*e10 - 36/31*e11 - 78/31*e13 - 36/31*e14 + 50/31*e15)],
         <function TorsorClassGroup.group_structure.<locals>.exp at 0x...>,
         <function TorsorClassGroup.group_structure.<locals>.log at 0x...>)
    """

    Element = Torsor

    def __init__(self, D, S):
        r"""
        INPUT:

        - `D` -- a dual pair of algebras over :math:`\mathbf{Q}`
        """
        self._dual_pair = D
        self._S = S
        AbelianGroupClass.__init__(self)

    def dual_pair(self):
        return self._dual_pair

    def _repr_(self):
        """
        Return a string representation of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: H = D.torsor_class_group([])
            sage: H
            Group of isomorphism classes of G-torsors where G is defined by
            Dual pair of algebras over Rational Field
            A = Finite flat algebra of degree 2 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
            B = Finite flat algebra of degree 2 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
        """
        s = "Group of isomorphism classes of G-torsors where G is defined by\n{}"
        return s.format(self._dual_pair)

    def _element_constructor_(self, T, tau):
        """
        Construct an element of `self`.
        """
        F = self._ext_group().simplicial_sheaf()
        if not F.is_valid_extension_datum(T, tau):
            raise ValueError("not a valid extension datum")
        return self.element_class(self, T, tau)

    @cached_method
    def _ext_group(self):
        from .ext_group import ExtGroupGm
        return ExtGroupGm(self.dual_pair().dual(), self._S)

    def one(self):
        """
        Return the unit element of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: H = D.torsor_class_group([])
            sage: H.one()
            Torsor defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e2 + e3)
        """
        one = self._ext_group().one()
        return self.element_class(self, one._T, one._tau)

    def order(self):
        """
        Return the order of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: H = D.torsor_class_group([])
            sage: H.order()
            2
        """
        return self.group_structure()[0].order()

    def gens(self):
        """
        Return a list of generators of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: H = D.torsor_class_group([])
            sage: H.gens()
            [Torsor defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e2 - e3)]
        """
        return self.group_structure()[1]

    def gens_orders(self):
        """
        Return a list of generators of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: H = D.torsor_class_group([])
            sage: H.gens_orders()
            (2,)
        """
        return self.group_structure()[0].gens_orders()

    def exp(self, x):
        return self.group_structure()[2](x)

    def log(self, x):
        return self.group_structure()[3](x)

    @cached_method
    def group_structure(self):
        r"""
        Return the group structure of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: from dual_pairs.dual_pair_from_dihedral_field import dual_pair_from_dihedral_field
            sage: R.<x> = QQ[]

            sage: A = FiniteFlatAlgebra(QQ, [x, x, x, x])
            sage: Phi = 1/4 * Matrix([[1, 1, -1, -1], [1, 1, 1, 1], [-1, 1, 1, -1], [-1, 1, -1, 1]])
            sage: D = DualPair(A, Phi)
            sage: H = D.torsor_class_group([])
            sage: H.group_structure()[0]
            Multiplicative Abelian group isomorphic to C2 x C2

            sage: D = dual_pair_from_dihedral_field(x^3 - x - 1, GF(2))
            sage: H = D.torsor_class_group([2, 23])
            sage: H.group_structure()
            (Multiplicative Abelian group isomorphic to C2 x C2,
             [Torsor defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 + 121/23*e5 + 2/23*e6 - 9/23*e7 + 2/23*e9 - 7/23*e10 + 43/23*e11 - 9/23*e13 + 43/23*e14 - 21/23*e15),
              Torsor defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 + 10/23*e5 + 11/23*e6 - 15/23*e7 + 11/23*e9 + 19/23*e10 - 5/23*e11 - 15/23*e13 - 5/23*e14 + 11/23*e15)],
             <function TorsorClassGroup.group_structure.<locals>.exp at 0x...>,
             <function TorsorClassGroup.group_structure.<locals>.log at 0x...>)

            sage: D = dual_pair_from_dihedral_field(x^3 + 4*x - 1, GF(2))
            sage: H = D.torsor_class_group([])
            sage: H.group_structure()
            (Multiplicative Abelian group isomorphic to C2 x C2,
             [Torsor defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 + 40/283*e5 + 41/283*e6 + 15/283*e7 + 41/283*e9 + 134/283*e10 - 20/283*e11 + 15/283*e13 - 20/283*e14 + 41/283*e15),
              Torsor defined by ((Fractional ideal (1), Fractional ideal (3, a + 1)), e0 + e1 + e4 + 1670/849*e5 - 19/283*e6 + 697/849*e7 - 19/283*e9 + 359/849*e10 + 14/849*e11 + 697/849*e13 + 14/849*e14 + 226/849*e15)],
             <function TorsorClassGroup.group_structure.<locals>.exp at 0x...>,
             <function TorsorClassGroup.group_structure.<locals>.log at 0x...>)

            # from elliptic curve 2184.j1
            # 2-descent shows that 2-Selmer group is isomorphic to (Z/2Z)^4
            # rank 1, torsion Z/2Z
            # Sha[2] is isomorphic to (Z/2Z)^2
            # factorisation of conductor: 2^3 * 3 * 7 * 13
            # Tamagawa numbers: 1, 1, 1, 2
            # so the only bad prime should be 13
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 - 42])
            sage: Phi = Matrix([[1/4, 1/4, 1/2, 0],
            ....:               [1/4, 1/4, -1/2, 0],
            ....:               [1/2, -1/2, 0, 0],
            ....:               [0, 0, 0, 42]])
            sage: D = DualPair(A, Phi)
            sage: H = D.torsor_class_group([13])
            sage: B, gens, exp, log = H.group_structure()
            sage: B
            Multiplicative Abelian group isomorphic to C2 x C2 x C2 x C2
            sage: exp(B.gen(0))
            Torsor defined by ((Fractional ideal (1), Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e2 + e4 + e5 + e6 + e8 + e9 - e10)
            sage: log(gens[1])
            f1
            sage: log(exp(B.gen(3))) == B.gen(3)
            True
        """
        E = self._ext_group()
        B, gens_E, exp_E, log_E = E.group_structure()
        C_to_B = E.commutative_subgroup()
        C = C_to_B.domain()

        def exp(x):
            e = exp_E(C_to_B(x))
            return self.element_class(self, e._T, e._tau)

        def log(T):
            e = E.element_class(E, T._T, T._tau)
            x = log_E(e)
            return C_to_B.inverse_image(x)

        gens = [exp(x) for x in C.gens()]

        return C, gens, exp, log
