# -*- coding: utf-8 -*-
r"""
Sheaves of Abelian groups.
"""

from __future__ import absolute_import

from sage.categories.functor import Functor

from .abelian_group_homomorphism import hom


class AbelianSheaf(Functor):
    """
    A sheaf of Abelian groups.

    INPUT:

    - `S` -- a finite set of primes
    """

    def __init__(self, S):
        from sage.categories.groups import Groups
        from sage.categories.rings import Rings
        self._S = S
        Functor.__init__(self, Rings().Commutative(), Groups().Commutative())

    def _apply_functor(self, A):
        return self._H0(A)[0]

    def _apply_functor_to_morphism(self, f):
        A = f.domain()
        B = f.codomain()
        H0_A, gens_H0_A, exp_H0_A, log_H0_A = self._H0(A)
        H0_B, gens_H0_B, exp_H0_B, log_H0_B = self._H0(B)
        return hom(H0_A, H0_B, [log_H0_B(self.map_section(f, s))
                                for s in gens_H0_A])


class MultiplicativeGroup(AbelianSheaf):
    """
    The multiplicative group as a sheaf of Abelian groups.

    INPUT:

    - `S` -- a finite set of primes
    """

    def _repr_(self):
        return "Multiplicative group"

    def _H0(self, A):
        from .unit_group import unit_group
        return unit_group(A, self._S)

    def _H1(self, A):
        from .class_group import class_group
        return class_group(A, self._S)

    def map_section(self, f, s):
        return f(s)

    def trivial_section(self, A):
        return A.one()

    def map_torsor(self, f, I):
        from .etale_algebra import map_ideal
        return map_ideal(f, I)

    def trivial_torsor(self, A):
        from .etale_algebra import ideal_monoid
        return ideal_monoid(A).one()

    def torsor_trivialisation(self, A, I):
        from .etale_algebra import ideal_generator
        return ideal_generator(A, self._S, I)

    def is_trivialisation(self, A, I, x):
        from .etale_algebra import ideal_is_generator
        return ideal_is_generator(A, self._S, I, x)


class RootsOfUnity(AbelianSheaf):
    """
    The sheaf of `n`-th roots of unity.

    INPUT:

    - `S` -- a finite set of primes

    - `n` -- a positive integer
    """

    def __init__(self, S, n):
        self._n = n
        AbelianSheaf.__init__(self, S)

    def _repr_(self):
        return "Sheaf of {} roots of unity".format(self._n.ordinal_str())

    def _H0(self, A):
        from .unit_group import roots_of_unity
        return roots_of_unity(A, self._n)

    def _H1(self, A):
        from .selmer_group import selmer_group
        return selmer_group(A, self._S, self._n)

    def map_section(self, f, s):
        return f(s)

    def trivial_section(self, A):
        return A.one()

    map_torsor = map_section

    def trivial_torsor(self, A):
        return A.one()

    def torsor_trivialisation(self, A, x):
        from .etale_algebra import nth_root
        return nth_root(A, x, self._n)

    def is_trivialisation(self, A, x, y):
        return x == y ** self._n
