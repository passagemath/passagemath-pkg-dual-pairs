# -*- coding: utf-8 -*-
r"""
Extensions of a finite group scheme by :math:`\mathbf{G}_{\mathrm{m}}`.
"""

from __future__ import absolute_import

from sage.groups.abelian_gps.abelian_group import AbelianGroup
from sage.groups.group import AbelianGroup as AbelianGroupClass
from sage.matrix.constructor import Matrix
from sage.misc.all import prod
from sage.misc.cachefunc import cached_method
from sage.rings.integer_ring import ZZ
from sage.structure.element import MultiplicativeGroupElement

from .abelian_group_homomorphism import hom, homology
from .etale_algebra import ideal_monoid, principal_ideal, ideal_generator, map_ideal
from .class_group import class_group
from .unit_group import unit_group

# TODO: move?
def tensor_maps(f, g):
    A = f.domain()
    C = f.codomain()
    B = g.domain()
    D = g.codomain()
    AB, _, _, _ = A.tensor_product(B)
    CD, _, _, t = C.tensor_product(D)
    return AB.hom([t(f(a), g(b)) for a in A.gens() for b in B.gens()], CD)

class ExtGroupElement(MultiplicativeGroupElement):

    def __init__(self, parent, ideal, tau):
        # TODO: need to check that the quotient between the two ideals
        # is the trivial ideal of A2 after inverting the primes in S
        # if parent._d1_ideal(ideal) != principal_ideal(parent._A2, tau):
        #     raise ValueError('tau does not generate d1(ideal)')
        if parent._d2_unit(tau) != parent._A3.one():
            raise ValueError('d2(tau) is non-trivial')
        self._ideal = ideal
        self._tau = tau
        MultiplicativeGroupElement.__init__(self, parent)

    def _repr_(self):
        return 'Group scheme extension defined by ({}, {})'.format(self._ideal, self._tau)

    def _mul_(self, other):
        E = self.parent()
        return E.element_class(E, self._ideal * other._ideal,
                               self._tau * other._tau)

    def __invert__(self):
        E = self.parent()
        return E.element_class(E, ~self._ideal, ~self._tau)

    def _to_H2_H(self):
        E = self.parent()
        UA2, gensUA2, exp_UA2, log_UA2 = E._unit_group_A2
        gen = ideal_generator(E._A, E._S, self._ideal)
        if gen is False:
            raise ValueError('{} is not in the Hochschild subgroup'.format(self))
        u = E._d1_unit(gen)
        tau = self._tau * ~u
        p, i = E._H2_H()
        return p(E.d2_U().kernel().inverse_image(log_UA2(tau)))

    # The following two functions need the group to be commutative.

    def opposite(self):
        E = self.parent()
        return E.element_class(E, self._ideal, E._swap()(self._tau))

    def sigma(self):
        tau = self._tau
        return self.parent()._swap()(tau) * ~tau


class ExtGroup(AbelianGroupClass):
    """
    The group of isomorphism classes of central extensions
    of a group scheme by the multiplicative group.

    EXAMPLES::

        sage: from dual_pairs import DualPair, FiniteFlatAlgebra
        sage: from dual_pairs.ext_group import ExtGroup
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x^3 - x^2 - 10*x + 8], [[1], [1, -x, -1/2*x^2 + 1/2*x + 3]])
        sage: Phi = 1/4 * Matrix([[1, 3, -1, -1], [3, -3, 1, 1], [-1, 1, 41, -21], [-1, 1, -21, 41]])
        sage: D = DualPair(A, Phi)
        sage: E = ExtGroup(D, [2]); E
        Group of central extensions of G by the multiplicative group
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
         <function ExtGroup.group_structure.<locals>.exp at 0x...>,
         <function ExtGroup.group_structure.<locals>.log at 0x...>)
    """

    Element = ExtGroupElement

    def __init__(self, D, S):
        r"""
        INPUT:

        - `D` -- a dual pair of algebras over :math:`\mathbf{Q}`

        - `S` -- a set of prime numbers
        """

        self._dual_pair = D
        self._S = S

        A = D.algebra1()
        A2, i0, i1, from_prod = A.tensor_product(A)
        A3 = A.tensor_product(A2)[0]
        e, mu = D.hopf_algebra()

        self._A = A
        self._A2 = A2
        self._A3 = A3

        self._unit_group_A = unit_group(A, S)
        self._unit_group_A2 = unit_group(A2, S)
        self._unit_group_A3 = unit_group(A3, S)

        self._class_group_A = class_group(A, S)
        self._class_group_A2 = class_group(A2, S)

        self._i0 = i0
        self._i1 = i1
        self._e = e
        self._mu = mu

        idA = A.hom(A)
        self._i01 = tensor_maps(idA, i0)
        self._i12 = tensor_maps(i1, idA)
        self._mu01 = tensor_maps(mu, idA)
        self._mu12 = tensor_maps(idA, mu)

        AbelianGroup.__init__(self)

    def _repr_(self):
        """
        Return a string representation of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: from dual_pairs.ext_group import ExtGroup
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: E = ExtGroup(D, [])
            sage: E
            Group of central extensions of G by the multiplicative group
            where G is defined by
            Dual pair of algebras over Rational Field
            A = Finite flat algebra of degree 2 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
            B = Finite flat algebra of degree 2 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x
        """
        return ("Group of central extensions of G by the multiplicative group\n"
                "where G is defined by\n" + repr(self._dual_pair))

    def _d1_unit(self, x):
        return self._i1(x) * ~self._mu(x) * self._i0(x)

    @cached_method
    def d1_U(self):
        UA, gensUA, exp_UA, log_UA = self._unit_group_A
        UA2, gensUA2, exp_UA2, log_UA2 = self._unit_group_A2

        return hom(UA, UA2, [log_UA2(self._d1_unit(x)) for x in gensUA])

    def _d2_unit(self, x):
        return self._i12(x) * ~self._mu01(x) * self._mu12(x) * ~self._i01(x)

    @cached_method
    def d2_U(self):
        UA2, gensUA2, exp_UA2, log_UA2 = self._unit_group_A2
        UA3, gensUA3, exp_UA3, log_UA3 = self._unit_group_A3

        return hom(UA2, UA3, [log_UA3(self._d2_unit(x)) for x in gensUA2])

    def _d1_ideal(self, I):
        return (map_ideal(self._i1, I) * ~map_ideal(self._mu, I)
                * map_ideal(self._i0, I))

    @cached_method
    def d1_Cl(self):
        ClA, gensClA, exp_ClA, log_ClA = self._class_group_A
        ClA2, gensClA2, exp_ClA2, log_ClA2 = self._class_group_A2

        return hom(ClA, ClA2, [log_ClA2(self._d1_ideal(I)) for I in gensClA])

    @cached_method
    def trg(self):
        ClA, gensClA, exp_ClA, log_ClA = self._class_group_A
        UA3, gensUA3, exp_UA3, log_UA3 = self._unit_group_A3

        # K(A) = ker(H^1(A, \Gm) -> H^1(A \otimes A, \Gm))
        ker_d1_Cl = self.d1_Cl().kernel()
        KA = ker_d1_Cl.domain()
        coker_d2_U = self.d2_U().cokernel()

        # Next we compute the "transgression" map from K(A) to the
        # Hochschild cohomology group H^3_H(A, \Gm).  Note that we
        # only need the cokernel of d^2, not the kernel of d^3.
        ideals_KA = [exp_ClA(ker_d1_Cl(v)) for v in KA.gens()]
        ideal_gens_KA = [ideal_generator(self._A2, self._S, self._d1_ideal(I))
                         for I in ideals_KA]
        images = [coker_d2_U(log_UA3(self._d2_unit(x)))
                  for x in ideal_gens_KA]
        return hom(KA, coker_d2_U.codomain(), images)

    @cached_method
    def _H2_H(self):
        """
        Return the Hochschild cohomology group `H^2_H(A, Gm)`.
        """
        return homology(self.d1_U(), self.d2_U())

    @cached_method
    def _KA_to_ClA(self):
        r"""
        Return the group `K(A)` together with the map to `Cl(A)`.
        """
        return self.d1_Cl().kernel()

    @cached_method
    def _LA_to_ClA(self):
        r"""
        Return the kernel `L(A)` of the "transgression" map from `K(A)` to
        the Hochschild cohomology group `H^3_H(A, Gm)`, together with
        the map to `Cl(A)`.
        """
        return self._KA_to_ClA() * self.trg().kernel()

    # injective homomorphism H^2_H(A, Gm) -> Ext(G, Gm)
    def _from_H2_H(self, x):
        UA2, gensUA2, exp_UA2, log_UA2 = self._unit_group_A2
        p, i = self._H2_H()
        u = exp_UA2(self.d2_U().kernel()(p.inverse_image(x)))
        I = ideal_monoid(self._A).one()
        return self.element_class(self, I, u)

    # set-theoretic section L(A) -> Ext(G, Gm)
    def _from_LA(self, x):
        ClA, gensClA, exp_ClA, log_ClA = self._class_group_A
        UA2, gensUA2, exp_UA2, log_UA2 = self._unit_group_A2
        UA3, gensUA3, exp_UA3, log_UA3 = self._unit_group_A3
        LA_to_ClA = self._LA_to_ClA()
        I = exp_ClA(LA_to_ClA(x))
        gen = ideal_generator(self._A2, self._S, self._d1_ideal(I))
        cocycle = log_UA3(self._d2_unit(gen))
        adj = exp_UA2(self.d2_U().inverse_image(cocycle))
        # now gen * ~adj has trivial d^2
        return self.element_class(self, I, gen * ~adj)

    def order(self):
        """
        Return the order of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: from dual_pairs.ext_group import ExtGroup
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: E = ExtGroup(D, [])
            sage: E.order()
            2
        """
        return self.group_structure()[0].order()

    def gens(self):
        """
        Return a list of generators of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: from dual_pairs.ext_group import ExtGroup
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: E = ExtGroup(D, [])
            sage: E.gens()
            [Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e2 - e3)]
        """
        return self.group_structure()[1]

    def gens_orders(self):
        """
        Return a list of generators of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: from dual_pairs.ext_group import ExtGroup
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x])
            sage: Phi = 1/2 * Matrix([[1, 1], [1, -1]])
            sage: D = DualPair(A, Phi)
            sage: E = ExtGroup(D, [])
            sage: E.gens_orders()
            (2,)
        """
        return self.group_structure()[0].gens_orders()

    def exp(self, x):
        return self.group_structure()[2](x)

    def log(self, x):
        return self.group_structure()[3](x)

    @cached_method
    def hochschild_subgroup(self):
        pass

    @cached_method
    def picard_quotient(self):
        pass

    @cached_method
    def _swap(self):
        A = self._A
        A2, _, _, from_prod = A.tensor_product(A)
        return A2.hom([from_prod(b, a) for a in A.basis() for b in A.basis()])

    @cached_method
    def group_structure(self):
        r"""
        Return the group structure of `self`.

        EXAMPLES::

            sage: from dual_pairs import DualPair, FiniteFlatAlgebra
            sage: from dual_pairs.dual_pair_from_dihedral_field import dual_pair_from_dihedral_field
            sage: from dual_pairs.ext_group import ExtGroup
            sage: R.<x> = QQ[]

            sage: A = FiniteFlatAlgebra(QQ, [x, x, x, x])
            sage: Phi = 1/4 * Matrix([[1, 1, -1, -1], [1, 1, 1, 1], [-1, 1, 1, -1], [-1, 1, -1, 1]])
            sage: D = DualPair(A, Phi)
            sage: E = ExtGroup(D, [])
            sage: E.group_structure()[0]
            Multiplicative Abelian group isomorphic to C2 x C2 x C2

            sage: D = dual_pair_from_dihedral_field(x^3 - x - 1, GF(2))
            sage: ExtGroup(D, [2, 23]).group_structure()
            (Multiplicative Abelian group isomorphic to C2 x C2 x C2,
             [Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 + 10/23*e5 + 11/23*e6 - 15/23*e7 + 11/23*e9 + 19/23*e10 - 5/23*e11 - 15/23*e13 - 5/23*e14 + 11/23*e15),
              Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e4 + 121/23*e5 + 2/23*e6 - 9/23*e7 + 2/23*e9 - 7/23*e10 + 43/23*e11 - 9/23*e13 + 43/23*e14 - 21/23*e15),
              Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1)), 23*e0 + 23*e1 + 23*e4 + 5/23*e5 + 40/23*e6 + 4/23*e7 - 52/23*e9 - 2/23*e10 + 78/23*e11 + 4/23*e13 - 60/23*e14 - 6/23*e15)],
             <function ExtGroup.group_structure.<locals>.exp at 0x...>,
             <function ExtGroup.group_structure.<locals>.log at 0x...>)

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
            sage: ExtGroup(D, [13]).group_structure()
            (Multiplicative Abelian group isomorphic to C2 x C2 x C2 x C2,
             [Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e2 + e4 + e5 + e6 + e8 + e9 - e10),
              Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e2 + e4 + e5 + 13*e6 - 2*e7 + e8 + 13*e9 + 7*e10 - e11 - 2*e13 - e14 + 1/7*e15),
              Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e2 + e4 + e5 + 41/13*e6 - 6/13*e7 + e8 + 41/13*e9 + 27*e10 - 3*e11 - 6/13*e13 - 3*e14 + 1/3*e15),
              Group scheme extension defined by ((Fractional ideal (1), Fractional ideal (1), Fractional ideal (1)), e0 + e1 + e2 + e4 + e5 + e6 + e8 + e9 + 13*e10)],
             <function ExtGroup.group_structure.<locals>.exp at 0x...>,
             <function ExtGroup.group_structure.<locals>.log at 0x...>)
        """
        UA, gensUA, exp_UA, log_UA = self._unit_group_A
        UA2, gensUA2, exp_UA2, log_UA2 = self._unit_group_A2
        UA3, gensUA3, exp_UA3, log_UA3 = self._unit_group_A3

        ClA, gensClA, exp_ClA, log_ClA = self._class_group_A
        ClA2, gensClA2, exp_ClA2, log_ClA2 = self._class_group_A2

        p, i = self._H2_H()
        H2_H = i.domain()  # == p.codomain()
        orders_H2_H = H2_H.gens_orders()

        ext_classes_H2_H = [self._from_H2_H(x) for x in H2_H.gens()]

        # K(A) = ker(d^1: H^1(A, \Gm) -> H^1(A \otimes A, \Gm))
        KA = self._KA_to_ClA().domain()

        # L(A) = ker(trg: K(A) -> H^3_H(A, Gm))
        LA = self._LA_to_ClA().domain()
        orders_LA = LA.gens_orders()

        ext_classes_LA = [self._from_LA(x) for x in LA.gens()]

        P = Matrix(ZZ, [(g ** o)._to_H2_H().exponents()
                        for g, o in zip(ext_classes_LA, orders_LA)],
                   ncols = H2_H.ngens())

        R = Matrix.block(ZZ, [[Matrix.diagonal(orders_H2_H), 0],
                              [P, Matrix.diagonal(orders_LA)]])
        S, U, V = R.smith_form()
        W = V.inverse_of_unit()
        orders = tuple(o for o in S.diagonal() if o != 1)

        if P != 0 or U != 1 or V != 1:
            raise NotImplementedError('non-trivial extension')

        B = AbelianGroup(orders)
        gens = ext_classes_H2_H + ext_classes_LA

        def exp(x):
            return prod(a * i for a, i in zip(gens, x.exponents()))

        def log(x):
            y = x._ideal
            w = exp_ClA(ideal).exponents()
            x0 = prod(a * i for a, i in zip(ext_classes_LA, w))
            v = (x * ~x0)._to_H2_H().exponents()
            return B(list(v) + list(w))

        return B, gens, exp, log

    @cached_method
    def commutative_subgroup(self):
        """
        Return the subgroup of `self` classifying commutative extensions.

        This requires the group scheme to be commutative.
        """
        B, gens, exp, log = self.group_structure()
        UA2, gensUA2, exp_UA2, log_UA2 = self._unit_group_A2
        M = Matrix(ZZ, [log_UA2(x.sigma()).exponents() for x in self.gens()])
        return hom(B, UA2, M).kernel()


# separate function because the class ExtGroupElement should support
# more general group schemes/sheaves instead of G_m
def extension_to_torsor(x):
    """
    Return a torsor pair corresponding to the extension `x`.

    INPUT:

    - `x` -- an extension (:class:`ExtGroupElement`)

    OUTPUT:

    A torsor pair for the dual group scheme.
    """
    from dual_pairs.torsor_pair import TorsorPair

    E = x.parent()
    D = E.dual_pair()
    D_dual = D.dual()
    ideal = x._ideal
    tau = x._tau
    raise NotImplementedError
