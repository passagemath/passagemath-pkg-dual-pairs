# -*- coding: utf-8 -*-
r"""
Simplicial sheaves.
"""

from __future__ import absolute_import

from sage.categories.functor import Functor
from sage.misc.cachefunc import cached_method

from .abelian_group_homomorphism import hom
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


class AbelianSheaf(Functor):
    def __init__(self):
        from sage.categories.groups import Groups
        from sage.categories.rings import Rings
        Functor.__init__(self, Rings().Commutative(), Groups().Commutative())


class MultiplicativeGroup(AbelianSheaf):

    def __init__(self, S):
        self._S = tuple(S)
        AbelianSheaf.__init__(self)

    def _apply_functor(self, A):
        return unit_group(A, self._S)[0]

    def _apply_functor_to_morphism(self, f):
        return NotImplemented


class SimplicialSheaf(AbelianSheaf):

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

        self._i0 = i0
        self._i1 = i1
        self._e = e
        self._mu = mu

        idA = A.hom(A)
        self._i01 = tensor_maps(idA, i0)
        self._i12 = tensor_maps(i1, idA)
        self._mu01 = tensor_maps(mu, idA)
        self._mu12 = tensor_maps(idA, mu)

        AbelianSheaf.__init__(self)

    @cached_method
    def swap(self):
        A = self._A
        A2, _, _, from_prod = A.tensor_product(A)
        return A2.hom([from_prod(b, a) for a in A.basis() for b in A.basis()])


class MultiplicativeSimplicialSheaf(SimplicialSheaf):

    def __init__(self, D, S):
        SimplicialSheaf.__init__(self, D, S)

        self._unit_group_A = unit_group(self._A, S)
        self._unit_group_A2 = unit_group(self._A2, S)
        self._unit_group_A3 = unit_group(self._A3, S)

        self._class_group_A = class_group(self._A, S)
        self._class_group_A2 = class_group(self._A2, S)

    @cached_method
    def H0(self, i):
        if i == 1:
            U = self._unit_group_A
        elif i == 2:
            U = self._unit_group_A2
        elif i == 3:
            U = self._unit_group_A3
        else:
            raise ValueError('unit group not computed for i = {}'.format(i))
        return U[0]

    @cached_method
    def H1(self, i):
        if i == 1:
            Cl = self._class_group_A
        elif i == 2:
            Cl = self._class_group_A2
        else:
            raise ValueError('class group not computed for i = {}'.format(i))
        return Cl[0]

    def trivial_torsor(self):
        return ideal_monoid(self._A).one()

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

    # TODO: name
    def exp_UA2(self):
        UA2, gensUA2, exp_UA2, log_UA2 = self._unit_group_A2
        return exp_UA2

    # TODO: name
    def log_UA2(self):
        UA2, gensUA2, exp_UA2, log_UA2 = self._unit_group_A2
        return log_UA2

    # TODO: name
    def exp_ClA(self):
        ClA, gensClA, exp_ClA, log_ClA = self._class_group_A
        return exp_ClA

    # TODO: name
    def log_ClA(self):
        ClA, gensClA, exp_ClA, log_ClA = self._class_group_A
        return log_ClA

    # TODO: name
    def to_H2_H_helper(self, I, tau):
        UA2, gensUA2, exp_UA2, log_UA2 = self._unit_group_A2
        gen = ideal_generator(self._A, self._S, I)
        if gen is False:
            raise ValueError('{} is not principal'.format(I))
        u = self._d1_unit(gen)
        return log_UA2(tau * ~u)

    # TODO: name
    def from_LA_helper(self, I):
        UA2, gensUA2, exp_UA2, log_UA2 = self._unit_group_A2
        UA3, gensUA3, exp_UA3, log_UA3 = self._unit_group_A3
        gen = ideal_generator(self._A2, self._S, self._d1_ideal(I))
        cocycle = log_UA3(self._d2_unit(gen))
        adj = exp_UA2(self.d2_U().inverse_image(cocycle))
        # now gen * ~adj has trivial d^2
        return gen * ~adj

    # TODO: name
    def trg_helper(self, x):
        ClA, gensClA, exp_ClA, log_ClA = self._class_group_A
        UA3, gensUA3, exp_UA3, log_UA3 = self._unit_group_A3

        I = exp_ClA(x)
        gen = ideal_generator(self._A2, self._S, self._d1_ideal(I))
        return log_UA3(self._d2_unit(gen))
