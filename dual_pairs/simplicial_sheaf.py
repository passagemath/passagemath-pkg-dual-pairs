# -*- coding: utf-8 -*-
r"""
Simplicial sheaves.
"""

from __future__ import absolute_import

from sage.misc.cachefunc import cached_method
from sage.structure.sage_object import SageObject

from .abelian_group_homomorphism import hom


def tensor_maps(f, g):
    A = f.domain()
    C = f.codomain()
    B = g.domain()
    D = g.codomain()
    AB, _, _, _ = A.tensor_product(B)
    CD, _, _, t = C.tensor_product(D)
    return AB.hom([t(f(a), g(b)) for a in A.gens() for b in B.gens()], CD)


class SimplicialSheaf(SageObject):
    r"""
    A simplicial sheaf for a dual pair of algebras.

    INPUT:

    - `D` -- a dual pair of algebras over :math:`\mathbf{Q}`

    - `F` -- a sheaf of Abelian groups (:class:`dual_pairs.abelian_sheaf.AbelianSheaf`)
    """

    def __init__(self, D, F):
        self._dual_pair = D
        self._sheaf = F

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

        SageObject.__init__(self)

    def sheaf(self):
        return self._sheaf

    @cached_method
    def swap(self):
        A = self._A[1]
        A2, _, _, from_prod = A.tensor_product(A)
        return A2.hom([from_prod(b, a) for a in A.basis() for b in A.basis()])

    @cached_method
    def _H0(self, i):
        return self.sheaf()._H0(self._A[i])

    @cached_method
    def _H1(self, i):
        return self.sheaf()._H1(self._A[i])

    def group_H0(self, i):
        return self._H0(i)[0]

    def exp_H0(self, i):
        return self._H0(i)[2]

    def log_H0(self, i):
        return self._H0(i)[3]

    def group_H1(self, i):
        return self._H1(i)[0]

    def exp_H1(self, i):
        return self._H1(i)[2]

    def log_H1(self, i):
        return self._H1(i)[3]

    def _d1_section(self, s):
        return (self.sheaf().map_section(self._i1, s)
                * ~self.sheaf().map_section(self._mu, s)
                * self.sheaf().map_section(self._i0, s))

    def _d2_section(self, s):
        return (self.sheaf().map_section(self._i12, s)
                * ~self.sheaf().map_section(self._mu01, s)
                * self.sheaf().map_section(self._mu12, s)
                * ~self.sheaf().map_section(self._i01, s))

    def _d1_torsor(self, T):
        return (self.sheaf().map_torsor(self._i1, T)
                * ~self.sheaf().map_torsor(self._mu, T)
                * self.sheaf().map_torsor(self._i0, T))

    @cached_method
    def d1_H0(self):
        H0_A, gens_H0_A, exp_H0_A, log_H0_A = self._H0(1)
        H0_A2, gens_H0_A2, exp_H0_A2, log_H0_A2 = self._H0(2)
        return hom(H0_A, H0_A2,
                   [log_H0_A2(self._d1_section(x)) for x in gens_H0_A])

    @cached_method
    def d2_H0(self):
        H0_A2, gens_H0_A2, exp_H0_A2, log_H0_A2 = self._H0(2)
        H0_A3, gens_H0_A3, exp_H0_A3, log_H0_A3 = self._H0(3)
        return hom(H0_A2, H0_A3,
                   [log_H0_A3(self._d2_section(x)) for x in gens_H0_A2])

    @cached_method
    def d1_H1(self):
        H1_A, gens_H1_A, exp_H1_A, log_H1_A = self._H1(1)
        H1_A2, gens_H1_A2, exp_H1_A2, log_H1_A2 = self._H1(2)
        return hom(H1_A, H1_A2,
                   [log_H1_A2(self._d1_torsor(T)) for T in gens_H1_A])

    def trivial_section(self, i):
        return self.sheaf().trivial_section(self._A[i])

    def trivial_torsor(self, i):
        return self.sheaf().trivial_torsor(self._A[i])

    def torsor_trivialisation(self, i, T):
        return self.sheaf().torsor_trivialisation(self._A[i], T)

    def is_valid_extension_datum(self, T, tau):
        F = self.sheaf()
        return (F.is_trivialisation(self._A[2], self._d1_torsor(T), tau)
                and self._d2_section(tau) == self.trivial_section(3))

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
