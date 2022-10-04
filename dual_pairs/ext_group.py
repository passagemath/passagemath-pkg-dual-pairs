# -*- coding: utf-8 -*-
r"""
Extensions of finite group schemes.
"""

from __future__ import absolute_import

from sage.groups.group import AbelianGroup as AbelianGroupClass
from sage.matrix.constructor import Matrix
from sage.misc.all import prod
from sage.misc.cachefunc import cached_method
from sage.rings.integer_ring import ZZ
from sage.structure.element import MultiplicativeGroupElement

from .abelian_group_homomorphism import hom, homology
from .smith_form import abelian_group_smith_form


class ExtGroupElement(MultiplicativeGroupElement):

    def __init__(self, parent, torsor, tau):
        self._T = torsor
        self._tau = tau
        MultiplicativeGroupElement.__init__(self, parent)

    def _repr_(self):
        return 'Group scheme extension defined by ({}, {})'.format(self._T, self._tau)

    def _mul_(self, other):
        E = self.parent()
        return E.element_class(E, self._T * other._T,
                               self._tau * other._tau)

    def __invert__(self):
        E = self.parent()
        return E.element_class(E, ~self._T, ~self._tau)

    def _to_H2_H(self):
        E = self.parent()
        F = E.simplicial_sheaf()
        x = F.to_H2_H_helper(self._T, self._tau)
        p, i = E._H2_H()
        return p(F.d2_H0().kernel().inverse_image(x))

    # The following two functions need the group to be commutative.

    def opposite(self):
        E = self.parent()
        F = E.simplicial_sheaf()
        return E.element_class(E, self._T, F.swap()(self._tau))

    def sigma(self):
        tau = self._tau
        return self.parent().simplicial_sheaf().swap()(tau) * ~tau


class ExtGroup(AbelianGroupClass):
    """
    The group of isomorphism classes of central extensions of a group
    scheme by a sheaf of Abelian groups.

    EXAMPLES::

        sage: from dual_pairs import DualPair, FiniteFlatAlgebra
        sage: from dual_pairs.ext_group import ExtGroupGm
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x^3 - x^2 - 10*x + 8], [[1], [1, -x, -1/2*x^2 + 1/2*x + 3]])
        sage: Phi = 1/4 * Matrix([[1, 3, -1, -1], [3, -3, 1, 1], [-1, 1, 41, -21], [-1, 1, -21, 41]])
        sage: D = DualPair(A, Phi)
        sage: E = ExtGroupGm(D, [2]); E
        Group of central extensions of G by Multiplicative group
        where G is defined by
        Dual pair of algebras over Rational Field
        A = Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^3 - x^2 - 10*x + 8
        B = Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^3 - x^2 - 10*x + 8
        sage: E.group_structure()
        (Multiplicative Abelian group isomorphic to C2 x C2 x C2 x C2 x C2,
         [Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 - 401/31*e5 - 102/31*e6 - 78/31*e7 - 102/31*e9 - 22/31*e10 - 36/31*e11 - 78/31*e13 - 36/31*e14 + 50/31*e15),
          Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 - 219/31*e5 + 38/31*e6 + 80/31*e7 + 38/31*e9 + 100/31*e10 + 14/31*e11 + 80/31*e13 + 14/31*e14 - 22/31*e15),
          Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 + 85/31*e5 - 52/31*e6 - 34/31*e7 - 52/31*e9 + 17/31*e10 + 13/31*e11 - 34/31*e13 + 13/31*e14 + 9/31*e15),
          Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 - 6/31*e5 + 14/31*e6 - 1/31*e7 + 14/31*e9 - 16/31*e10 - 4/31*e11 - 1/31*e13 - 4/31*e14 + 1/31*e15),
          Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), 2*e0 + 2*e1 + 2*e4 + 13/31*e5 - 19/31*e6 - 4/31*e7 + 37/31*e9 - 1/31*e10 - 12/31*e11 + 2/31*e13 + 6/31*e14)],
         <function abelian_group_smith_form.<locals>.exp at 0x...>,
         <function abelian_group_smith_form.<locals>.log at 0x...>)
    """

    Element = ExtGroupElement

    def __init__(self, D, F):
        r"""
        INPUT:

        - `D` -- a dual pair of algebras over :math:`\mathbf{Q}`

        - `F` -- a sheaf of Abelian groups (:class:`dual_pairs.abelian_sheaf.AbelianSheaf`)
        """
        self._dual_pair = D
        self._sheaf = F
        AbelianGroupClass.__init__(self)

    def dual_pair(self):
        return self._dual_pair

    def sheaf(self):
        return self._sheaf

    def _repr_(self):
        """
        Return a string representation of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: from dual_pairs.ext_group import ExtGroupGm
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: E = ExtGroupGm(D, [])
            sage: E
            Group of central extensions of G by Multiplicative group
            where G is defined by
            Dual pair of algebras over Rational Field
            A = Finite flat algebra of degree 2 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
            B = Finite flat algebra of degree 2 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
        """
        s = "Group of central extensions of G by {}\nwhere G is defined by\n{}"
        return s.format(self._sheaf, self._dual_pair)

    @cached_method
    def simplicial_sheaf(self):
        from .simplicial_sheaf import SimplicialSheaf
        return SimplicialSheaf(self._dual_pair, self._sheaf)

    def _element_constructor_(self, T, tau):
        """
        Construct an element of `self`.
        """
        F = self.simplicial_sheaf()
        if not F.is_valid_extension_datum(torsor, tau):
            raise ValueError("not a valid extension datum")
        return self.element_class(self, T, tau)

    def one(self):
        """
        Return the unit element of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: from dual_pairs.ext_group import ExtGroup_mu_n
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: E = ExtGroup_mu_n(D, [], 2)
            sage: E.one()
            Group scheme extension defined by ((1, 1), e0 + e1 + e2 + e3)
        """
        F = self.simplicial_sheaf()
        T = F.trivial_torsor(1)
        tau = F.trivial_section(2)
        return self.element_class(self, T, tau)

    def _K_to_H1(self):
        r"""
        Return the group `K(G, F)` together with the map to `H^1(G, F)`.
        """
        F = self.simplicial_sheaf()
        return F.d1_H1().kernel()

    @cached_method
    def trg(self):
        F = self.simplicial_sheaf()

        # K(G, F) = ker(d^1: H^1(G, F) -> H^1(G^2, F))
        K_to_H1 = self._K_to_H1()
        K = K_to_H1.domain()
        coker_d2_H0 = F.d2_H0().cokernel()

        # Next we compute the "transgression" map from K(G, F) to the
        # Hochschild cohomology group H^3_H(G, F).  Note that we
        # only need the cokernel of d^2, not the kernel of d^3.
        images = [coker_d2_H0(F.trg_helper(K_to_H1(v))) for v in K.gens()]
        return hom(K, coker_d2_H0.codomain(), images)

    @cached_method
    def _H2_H(self):
        """
        Return the Hochschild cohomology group `H^2_H(G, F)`.
        """
        F = self.simplicial_sheaf()
        return homology(F.d1_H0(), F.d2_H0())

    @cached_method
    def _L_to_H1(self):
        r"""
        Return the kernel `L(G, F)` of the "transgression" map from
        `K(G, F)` to the Hochschild cohomology group `H^3_H(G, F)`,
        together with the map to `H^1(G, F)`.
        """
        return self._K_to_H1() * self.trg().kernel()

    # injective homomorphism H^2_H(G, F) -> Ext(G, F)
    def _from_H2_H(self, x):
        F = self.simplicial_sheaf()
        T = F.trivial_torsor(1)
        p, i = self._H2_H()
        tau = F.exp_H0(2)(F.d2_H0().kernel()(p.inverse_image(x)))
        return self.element_class(self, T, tau)

    # set-theoretic section L(G, F) -> Ext(G, F)
    def _from_L(self, x):
        F = self.simplicial_sheaf()
        L_to_H1 = self._L_to_H1()
        T = F.exp_H1(1)(L_to_H1(x))
        gen = F.from_L_helper(T)
        return self.element_class(self, T, gen)

    def order(self):
        """
        Return the order of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: from dual_pairs.ext_group import ExtGroupGm
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: E = ExtGroupGm(D, [])
            sage: E.order()
            2
        """
        return self.group_structure()[0].order()

    def gens(self):
        """
        Return a list of generators of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: from dual_pairs.ext_group import ExtGroupGm
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: E = ExtGroupGm(D, [])
            sage: E.gens()
            [Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e2 - e3)]
        """
        return self.group_structure()[1]

    def gens_orders(self):
        """
        Return a list of generators of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: from dual_pairs.ext_group import ExtGroupGm
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: E = ExtGroupGm(D, [])
            sage: E.gens_orders()
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
            sage: from dual_pairs.ext_group import ExtGroupGm
            sage: R.<x> = QQ[]

            sage: A = FiniteFlatAlgebra(QQ, [x, x, x, x])
            sage: Phi = 1/4 * Matrix([[1, 1, -1, -1], [1, 1, 1, 1], [-1, 1, 1, -1], [-1, 1, -1, 1]])
            sage: D = DualPair(A, Phi)
            sage: E = ExtGroupGm(D, [])
            sage: E.group_structure()[0]
            Multiplicative Abelian group isomorphic to C2 x C2 x C2

            sage: D = dual_pair_from_dihedral_field(x^3 - x - 1, GF(2))
            sage: E = ExtGroupGm(D, [2, 23])
            sage: E.group_structure()
            (Multiplicative Abelian group isomorphic to C2 x C2 x C2,
             [Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 + 10/23*e5 + 11/23*e6 - 15/23*e7 + 11/23*e9 + 19/23*e10 - 5/23*e11 - 15/23*e13 - 5/23*e14 + 11/23*e15),
              Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 + 121/23*e5 + 2/23*e6 - 9/23*e7 + 2/23*e9 - 7/23*e10 + 43/23*e11 - 9/23*e13 + 43/23*e14 - 21/23*e15),
              Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), 23*e0 + 23*e1 + 23*e4 + 5/23*e5 + 40/23*e6 + 4/23*e7 - 52/23*e9 - 2/23*e10 + 78/23*e11 + 4/23*e13 - 60/23*e14 - 6/23*e15)],
             <function abelian_group_smith_form.<locals>.exp at 0x...>,
             <function abelian_group_smith_form.<locals>.log at 0x...>)

            sage: D = dual_pair_from_dihedral_field(x^3 + 4*x - 1, GF(2))
            sage: E = ExtGroupGm(D, [])
            sage: E.group_structure()
            (Multiplicative Abelian group isomorphic to C2 x C2,
             [Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 + 40/283*e5 + 41/283*e6 + 15/283*e7 + 41/283*e9 + 134/283*e10 - 20/283*e11 + 15/283*e13 - 20/283*e14 + 41/283*e15),
              Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (3, a + 1)), e0 + e1 + e4 + 1670/849*e5 - 19/283*e6 + 697/849*e7 - 19/283*e9 + 359/849*e10 + 14/849*e11 + 697/849*e13 + 14/849*e14 + 226/849*e15)],
             <function abelian_group_smith_form.<locals>.exp at 0x...>,
             <function abelian_group_smith_form.<locals>.log at 0x...>)

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
            sage: E = ExtGroupGm(D, [13])
            sage: B, gens, exp, log = E.group_structure()
            sage: B
            Multiplicative Abelian group isomorphic to C2 x C2 x C2 x C2
            sage: exp(B.gen(0))
            Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e2 + e4 + e5 + e6 + e8 + e9 - e10)
            sage: log(gens[1])
            f1
            sage: log(exp(B.gen(3))) == B.gen(3)
            True
        """
        p, i = self._H2_H()
        H2_H = i.domain()  # == p.codomain()

        # L(G, F) = ker(trg: K(G, F) -> H^3_H(G, F))
        L = self._L_to_H1().domain()

        gens_H2_H = [self._from_H2_H(x) for x in H2_H.gens()]
        gens_L = [self._from_L(x) for x in L.gens()]
        gens = gens_H2_H + gens_L

        P = Matrix(ZZ, L.ngens(), H2_H.ngens(),
                   [(g ** o)._to_H2_H().exponents()
                    for g, o in zip(gens_L, L.gens_orders())])
        R = Matrix.block(ZZ, [[Matrix.diagonal(H2_H.gens_orders()), 0],
                              [P, Matrix.diagonal(L.gens_orders())]])

        def log(x):
            F = self.simplicial_sheaf()
            w = F.log_H1(1)(x._T).exponents()
            y = prod((a ** -i for a, i in zip(gens_L, w)), x)
            v = y._to_H2_H().exponents()
            return list(v) + list(w)

        return abelian_group_smith_form(R, self.one(), gens, log)

    @cached_method
    def commutative_subgroup(self):
        """
        Return the subgroup of `self` classifying commutative extensions.

        This requires the group scheme to be commutative.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: from dual_pairs.ext_group import ExtGroupGm
            sage: R.<x> = QQ[]

            sage: A = FiniteFlatAlgebra(QQ, [x, x, x, x])
            sage: Phi = 1/4 * Matrix([[1, 1, -1, -1], [1, 1, 1, 1], [-1, 1, 1, -1], [-1, 1, -1, 1]])
            sage: D = DualPair(A, Phi)
            sage: E = ExtGroupGm(D, [])
            sage: E.commutative_subgroup()
            Abelian group morphism:
              From: Multiplicative Abelian group isomorphic to C2 x C2
              To:   Multiplicative Abelian group isomorphic to C2 x C2 x C2
            Defn:
              f0 |--> f0
              f1 |--> f2
        """
        F = self.simplicial_sheaf()
        B, gens, exp, log = self.group_structure()
        M = Matrix(ZZ, [F.log_H0(2)(x.sigma()).exponents() for x in gens])
        return hom(B, F.group_H0(2), M).kernel()


def ExtGroupGm(D, S):
    r"""
    Return the group of isomorphism classes of central extensions of a
    group scheme by the multiplicative group.

    INPUT:

    - `D` -- a dual pair of algebras over :math:`\mathbf{Q}`

    - `S` -- a finite set of prime numbers

        sage: from dual_pairs import DualPair, FiniteFlatAlgebra
        sage: from dual_pairs.ext_group import ExtGroupGm
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x])
        sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
        sage: D = DualPair(A, Phi)
        sage: ExtGroupGm(D, [])
        Group of central extensions of G by Multiplicative group
        where G is defined by
        Dual pair of algebras over Rational Field
        A = Finite flat algebra of degree 2 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x
        B = Finite flat algebra of degree 2 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x
    """
    from .abelian_sheaf import MultiplicativeGroup
    return ExtGroup(D, MultiplicativeGroup(S))


def ExtGroup_mu_n(D, S, n):
    r"""
    Return the group of isomorphism classes of central extensions of a
    group scheme by the sheaf of `n`-th roots of unity.

    INPUT:

    - `D` -- a dual pair of algebras over :math:`\mathbf{Q}`

    - `S` -- a finite set of prime numbers

    - `n` -- a positive integer

    EXAMPLES::

        sage: from dual_pairs import DualPair, FiniteFlatAlgebra
        sage: from dual_pairs.ext_group import ExtGroup_mu_n
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x])
        sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
        sage: D = DualPair(A, Phi)
        sage: E = ExtGroup_mu_n(D, [], 2)
        sage: E
        Group of central extensions of G by Sheaf of 2nd roots of unity
        where G is defined by
        Dual pair of algebras over Rational Field
        A = Finite flat algebra of degree 2 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x
        B = Finite flat algebra of degree 2 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x
        sage: E.group_structure()
        (Multiplicative Abelian group isomorphic to C2 x C2,
         [Group scheme extension defined by ((1, 1), e0 + e1 + e2 - e3),
          Group scheme extension defined by ((1, -1), e0 + e1 + e2 + e3)],
         <function abelian_group_smith_form.<locals>.exp at 0x...>,
         <function abelian_group_smith_form.<locals>.log at 0x...>)
    """
    from .abelian_sheaf import RootsOfUnity
    mu_n = RootsOfUnity(S, n)
    return ExtGroup(D, mu_n)
