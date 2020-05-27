# -*- coding: utf-8 -*-
r"""
Commutative extensions of :math:`\mathbf{Z}/m\mathbf{Z}` by
:math:`\mu_n` over a ring :math:`R`.

If the Picard group of :math:`R` is trivial, such extensions are
classified up to isomorphism by pairs :math:`(a, b) \in R^\times
\times R^\times` satisfying :math:`a^m b^n=1`, modulo the action of
:math:`R^\times` defined by :math:`c(a,b)=(c^{-n} a,c^m b)`.
"""

from __future__ import absolute_import

from sage.matrix.constructor import Matrix
from sage.rings.polynomial.polynomial_ring import polygen

from dual_pairs import FiniteFlatAlgebra, DualPair

def extension(R, m, n, a, b):
    r"""
    Return the extension of :math:`\mathbf{Z}/m\mathbf{Z}` by
    :math:`\mu_n` over `R` defined by the pair :math:`(a,b)`.

    EXAMPLES::

        sage: from dual_pairs.extension import extension

        sage: E = extension(QQ, 2, 2, 17, 1/17)
        sage: L.<u> = E.splitting_field(); L
        Number Field in u with defining polynomial t^2 - t - 4
        sage: E.group_structure(L)[0]
        Additive abelian group isomorphic to Z/2 + Z/2

        sage: F = extension(QQ, 2, 2, 17, -1/17)
        sage: M.<v> = F.splitting_field(); M
        Number Field in v with defining polynomial t^4 + 1156
        sage: F.group_structure(M)[0]
        Additive abelian group isomorphic to Z/4

        sage: G = extension(QQ, 2, 3, 5^3, 1/5^2)
        sage: T.<v> = G.splitting_field(); T
        Number Field in v with defining polynomial t^2 + 4*t + 31
        sage: G.group_structure(T)[0]
        Additive abelian group isomorphic to Z/6

        sage: E = extension(QQ, 3, 3, 7, 1/7)
        sage: L.<a> = E.splitting_field(); L
        Number Field in a with defining polynomial t^6 ...
        sage: L.is_abelian()
        False
        sage: E.group_structure(L)[0]
        Additive abelian group isomorphic to Z/3 + Z/3

        sage: H = extension(QQ, 5, 3, 2^3, 1/2^5)
        sage: U.<v> = H.splitting_field(); U
        Number Field in v with defining polynomial t^8 ...
        sage: U.discriminant().factor()
        3^4 * 5^6
        sage: U.conductor()
        15
        sage: H.group_structure(U)[0]
        Additive abelian group isomorphic to Z/15

        sage: J = extension(QQ, 4, 6, 8, 1/4)
        sage: V.<a> = J.splitting_field(); V
        Number Field in a with defining polynomial t^8 ...
        sage: V.discriminant().factor()
        2^16 * 3^4
        sage: V.conductor()
        24
        sage: J.group_structure(V)[0]
        Additive abelian group isomorphic to Z/12 + Z/2
    """
    if a**m * b**n != R.one():
        raise ValueError("(a, b, m, n) = {} does not satisfy a^m * b^n = 1".format((a, b, m, n)))
    t = polygen(R, 't')
    u = polygen(R, 'u')
    A = FiniteFlatAlgebra(R, [t**n - a**i for i in range(m)])
    B = FiniteFlatAlgebra(R, [u**m - b**j for j in range(n)])
    Phi = Matrix.zero(R, m*n, m*n)
    for i in range(m):
        for j in range(n):
            Phi[j + n*i, i + m*j] = R.one()
    Phi.set_immutable()
    return DualPair(A, B, Phi)
