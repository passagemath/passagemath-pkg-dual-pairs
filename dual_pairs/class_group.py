# -*- coding: utf-8 -*-
r"""
Class groups of finite flat algebras
"""

from __future__ import absolute_import

from sage.categories.cartesian_product import cartesian_product
from sage.groups.abelian_gps.abelian_group import AbelianGroup
from sage.misc.all import prod

from .etale_algebra import isom_to_etale_algebra

def _split_list(v, lengths):
    s = []
    for l in lengths:
        s.append(v[:l])
        v = v[l:]
    return s

def _S_class_group(K, S):
    Cl = K.S_class_group(S)
    Cl_gens = Cl.gens_values()

    def from_Cl(x):
        return prod((c**e for c, e in zip(Cl.gens_values(), x)),
                    K.fractional_ideal(1))

    def to_Cl(I):
        return Cl(I).exponents()

    return Cl, Cl_gens, from_Cl, to_Cl

def class_group(A, S):
    """
    Return the `S`-class group of `A`.

    This is a version for étale algebras of the method
    :meth:`NumberField.S_class_group`.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: from dual_pairs.class_group import class_group
        sage: from dual_pairs.etale_algebra import ideal_generator
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x^2 + 23])
        sage: S = [5]
        sage: Cl, gens, from_Cl, to_Cl = class_group(A, S)
        sage: c = Cl.random_element(); c   # random
        f^2
        sage: I = from_Cl(c); I            # random
        (Fractional ideal (1), Fractional ideal (4, 1/2*a + 3/2))
        sage: to_Cl(I) == c
        True
        sage: ideal_generator(A, S, I^-3)  # random
        (1, -3/128*a1 - 7/128)
    """
    Sprod = prod(S)
    to_P, from_P = isom_to_etale_algebra(A)
    P = from_P.domain()
    factors = P.cartesian_factors()
    r = len(factors)

    class_groups = [_S_class_group(K, K.primes_above(Sprod)) for K in factors]
    Cl, Cl_gens, from_Cl, to_Cl = zip(*class_groups)

    nfactors = [C.ngens() for C in Cl]
    orders = [list(C.gens_orders()) for C in Cl]

    ClA = AbelianGroup(sum(orders, []))

    P = cartesian_product([K.ideal_monoid() for K in factors])

    gens = []
    for i, g in enumerate(Cl_gens):
        gens.extend([P([a if j == i else factors[j].fractional_ideal(1)
                        for j in range(r)])
                     for a in g])

    def from_ClA(x):
        y = _split_list(x.exponents(), nfactors)
        return P([f(v) for f, v in zip(from_Cl, y)])

    def to_ClA(I):
        return ClA(sum((list(g(J)) for g, J in zip(to_Cl, I)), []))

    return ClA, gens, from_ClA, to_ClA
