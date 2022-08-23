# -*- coding: utf-8 -*-
r"""
Selmer groups of finite flat algebras
"""

from __future__ import absolute_import

from sage.groups.abelian_gps.abelian_group import AbelianGroup
from sage.misc.all import prod
from sage.rings.rational_field import QQ

from .etale_algebra import isom_to_etale_algebra

def _split_list(v, lengths):
    s = []
    for l in lengths:
        s.append(v[:l])
        v = v[l:]
    return s

def _primes_above(K, m):
    if K is QQ:
        return m.prime_factors()
    else:
        return K.primes_above(m)

def selmer_group(A, S, p):
    """
    Return the `p`-Selmer group of `A` relative to `S`.

    This is a version for étale algebras of the method
    :meth:`NumberField.selmer_space`.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: from dual_pairs.selmer_group import selmer_group
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x^3 - x - 1])
        sage: S = [2, 23]
        sage: Sel, gens, from_Sel, to_Sel = selmer_group(A, S, 2)
        sage: v = Sel.random_element()
        sage: to_Sel(from_Sel(v)) == v
        True
    """
    Sprod = prod(S)
    to_P, from_P = isom_to_etale_algebra(A)
    P = from_P.domain()
    factors = P.cartesian_factors()
    r = len(factors)

    selmer_spaces = [K.selmer_space(_primes_above(K, Sprod), p) for K in factors]
    Sel, Sel_gens, from_Sel, to_Sel = zip(*selmer_spaces)

    dimensions = [V.dimension() for V in Sel]

    SelP = AbelianGroup([p] * sum(dimensions))

    gens = []
    for i, g in enumerate(Sel_gens):
        gens.extend([from_P([1] * i + [a] + [1] * (r - i - 1)) for a in g])

    def from_SelP(x):
        y = _split_list(x.exponents(), dimensions)
        return from_P([f(z) for f, z in zip(from_Sel, y)])

    def to_SelP(x):
        return SelP(sum((list(h(z)) for h, z in zip(to_Sel, to_P(x))), []))

    return SelP, gens, from_SelP, to_SelP
