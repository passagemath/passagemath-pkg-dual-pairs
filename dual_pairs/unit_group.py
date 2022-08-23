# -*- coding: utf-8 -*-
r"""
Unit groups of finite flat algebras
"""

from __future__ import absolute_import

from sage.groups.abelian_gps.abelian_group import AbelianGroup
from sage.misc.all import prod

from .etale_algebra import isom_to_etale_algebra

def _split_list(v, lengths):
    s = []
    for l in lengths:
        s.append(v[:l])
        v = v[l:]
    return s

def _S_unit_group(K, S):
    U = K.S_unit_group(S=S)
    U_gens = U.gens_values()

    def from_U(u):
        return U.exp(u)

    def to_U(x):
        return U(x).exponents()

    return U, U_gens, from_U, to_U

def _mu_n(K, n):
    n = n.gcd(K.zeta_order())
    mu = K.zeta(n).powers(n)

    def exp(i):
        return mu[i]

    def log(x):
        return mu.index(x)

    return K.zeta(n), n, exp, log

def unit_group(A, S):
    """
    Return the `S`-unit group of `A`.

    This is a version for étale algebras of the method
    :meth:`NumberField.S_unit_group`.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: from dual_pairs.unit_group import unit_group
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x^2 + 23])
        sage: S = [5]
        sage: U, gens, from_U, to_U = unit_group(A, S)
        sage: U
        Multiplicative Abelian group isomorphic to C2 x Z x C2 x Z
        sage: gens
        [(-1, 1), (5, 1), (1, -1), (1, 5)]
        sage: u = U([1, 4, 1, 6])
        sage: v = from_U(u)
        sage: to_U(v) == u
        True
    """
    Sprod = prod(S)
    to_P, from_P = isom_to_etale_algebra(A)
    P = from_P.domain()
    factors = P.cartesian_factors()
    r = len(factors)

    unit_groups = [_S_unit_group(K, K.primes_above(Sprod)) for K in factors]
    U, U_gens, from_U, to_U = zip(*unit_groups)

    nfactors = [C.ngens() for C in U]
    orders = [list(C.gens_orders()) for C in U]

    UA = AbelianGroup(sum(orders, []))

    gens = []
    for i, g in enumerate(U_gens):
        gens.extend([from_P([1] * i + [a] + [1] * (r - i - 1)) for a in g])

    def from_UA(x):
        y = _split_list(x.exponents(), nfactors)
        return from_P([f(v) for f, v in zip(from_U, y)])

    def to_UA(x):
        return UA(sum((list(g(y)) for g, y in zip(to_U, to_P(x))), []))

    return UA, gens, from_UA, to_UA

def roots_of_unity(A, n):
    """
    Return the group of `n`-th roots of unity of `A`.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: from dual_pairs.unit_group import roots_of_unity
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x^2 + x + 1])
        sage: mu, gens, exp_mu, log_mu = roots_of_unity(A, 6)
        sage: mu
        Multiplicative Abelian group isomorphic to C2 x C6
        sage: gens
        [(-1, 1), (1, a1 + 1)]
    """
    to_P, from_P = isom_to_etale_algebra(A)
    P = from_P.domain()
    factors = P.cartesian_factors()
    r = len(factors)

    zetas, orders, exp, log = zip(*(_mu_n(K, n) for K in factors))

    mu = AbelianGroup(orders)
    gens = [from_P([1] * i + [x] + [1] * (r - i - 1))
            for i, x in enumerate(zetas)]

    def exp_mu(x):
        y = x.exponents()
        return from_P([f(v) for f, v in zip(exp, y)])

    def log_mu(x):
        return mu([g(y) for g, y in zip(log, to_P(x))])

    return mu, gens, exp_mu, log_mu
