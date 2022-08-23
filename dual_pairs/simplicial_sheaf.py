# -*- coding: utf-8 -*-
r"""
Simplicial sheaves.
"""

from __future__ import absolute_import

from sage.categories.functor import Functor
from sage.misc.cachefunc import cached_method

from .abelian_group_homomorphism import hom


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


class SimplicialSheaf(AbelianSheaf):

    def __init__(self, D, S):
        r"""
        INPUT:

        - `D` -- a dual pair of algebras over :math:`\mathbf{Q}`

        - `S` -- a set of prime numbers
        """

        self._dual_pair = D
        self._S = tuple(S)

        A = D.algebra1()
        A2, i0, i1, from_prod = A.tensor_product(A)
        A3 = A.tensor_product(A2)[0]
        e, mu = D.hopf_algebra()

        self._A = (None, A, A2, A3)

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

    def _apply_functor(self, A):
        return self._H0(A)[0]

    def _apply_functor_to_morphism(self, f):
        return NotImplemented

    @cached_method
    def swap(self):
        A = self._A[1]
        A2, _, _, from_prod = A.tensor_product(A)
        return A2.hom([from_prod(b, a) for a in A.basis() for b in A.basis()])

    def H0(self, i):
        return self._H0(self._A[i])[0]

    def H1(self, i):
        return self._H1(self._A[i])[0]

    def exp_H0(self, i):
        return self._H0(self._A[i])[2]

    def log_H0(self, i):
        return self._H0(self._A[i])[3]

    def exp_H1(self, i):
        return self._H1(self._A[i])[2]

    def log_H1(self, i):
        return self._H1(self._A[i])[3]

    @cached_method
    def d1_H0(self):
        H0_A, gens_H0_A, exp_H0_A, log_H0_A = self._H0(self._A[1])
        H0_A2, gens_H0_A2, exp_H0_A2, log_H0_A2 = self._H0(self._A[2])
        return hom(H0_A, H0_A2,
                   [log_H0_A2(self._d1_section(x)) for x in gens_H0_A])

    @cached_method
    def d2_H0(self):
        H0_A2, gens_H0_A2, exp_H0_A2, log_H0_A2 = self._H0(self._A[2])
        H0_A3, gens_H0_A3, exp_H0_A3, log_H0_A3 = self._H0(self._A[3])
        return hom(H0_A2, H0_A3,
                   [log_H0_A3(self._d2_section(x)) for x in gens_H0_A2])

    @cached_method
    def d1_H1(self):
        H1_A, gens_H1_A, exp_H1_A, log_H1_A = self._H1(self._A[1])
        H1_A2, gens_H1_A2, exp_H1_A2, log_H1_A2 = self._H1(self._A[2])
        return hom(H1_A, H1_A2,
                   [log_H1_A2(self._d1_torsor(T)) for T in gens_H1_A])

    # TODO: name
    def to_H2_H_helper(self, T, tau):
        log_H0_A2 = self.log_H0(2)
        gen = self.torsor_trivialisation(1, T)
        u = self._d1_section(gen)
        return log_H0_A2(tau * ~u)

    # TODO: name
    def from_L_helper(self, T):
        exp_H0_A2 = self.exp_H0(2)
        log_H0_A3 = self.log_H0(3)
        gen = self.torsor_trivialisation(2, self._d1_torsor(T))
        cocycle = log_H0_A3(self._d2_section(gen))
        adj = exp_H0_A2(self.d2_H0().inverse_image(cocycle))
        # now gen * ~adj has trivial d^2
        return gen * ~adj

    # TODO: name
    def trg_helper(self, x):
        exp_H1_A = self.exp_H1(1)
        log_H0_A3 = self.log_H0(3)
        gen = self.torsor_trivialisation(2, self._d1_torsor(exp_H1_A(x)))
        return log_H0_A3(self._d2_section(gen))


class MultiplicativeSimplicialSheaf(SimplicialSheaf):

    def _repr_(self):
        return "Multiplicative group"

    @cached_method
    def _H0(self, A):
        from .unit_group import unit_group
        return unit_group(A, self._S)

    @cached_method
    def _H1(self, A):
        from .class_group import class_group
        return class_group(A, self._S)

    def trivial_torsor(self):
        from .etale_algebra import ideal_monoid
        return ideal_monoid(self._A[1]).one()

    def torsor_trivialisation(self, i, I):
        from .etale_algebra import ideal_generator
        return ideal_generator(self._A[i], self._S, I)

    def _d1_section(self, x):
        return self._i1(x) * ~self._mu(x) * self._i0(x)

    def _d2_section(self, x):
        return self._i12(x) * ~self._mu01(x) * self._mu12(x) * ~self._i01(x)

    def _d1_torsor(self, I):
        from .etale_algebra import map_ideal
        return (map_ideal(self._i1, I) * ~map_ideal(self._mu, I)
                * map_ideal(self._i0, I))


class RootsOfUnitySimplicialSheaf(SimplicialSheaf):

    def __init__(self, D, S, n):
        self._n = n
        SimplicialSheaf.__init__(self, D, S)

    def _repr_(self):
        return "Sheaf of {} roots of unity".format(self._n.ordinal_str())

    @cached_method
    def _H0(self, A):
        from .unit_group import roots_of_unity
        return roots_of_unity(A, self._n)

    @cached_method
    def _H1(self, A):
        from .selmer_group import selmer_group
        return selmer_group(A, self._S, self._n)

    def trivial_torsor(self):
        return self._A[1].one()

    def torsor_trivialisation(self, i, x):
        from .etale_algebra import nth_root
        return nth_root(self._A[i], x, self._n)

    def _d1_section(self, x):
        return self._i1(x) * ~self._mu(x) * self._i0(x)

    def _d2_section(self, x):
        return self._i12(x) * ~self._mu01(x) * self._mu12(x) * ~self._i01(x)

    _d1_torsor = _d1_section
