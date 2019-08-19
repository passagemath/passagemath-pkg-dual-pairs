# -*- coding: utf-8 -*-
"""
Import a dual pair of algebras from a file.
"""

from __future__ import absolute_import

from sage.libs.pari import pari
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ

from .dual_pair import DualPair
from .finite_flat_algebra import FiniteFlatAlgebra

def dual_pair_import(file):
    """
    TODO
    """
    data = pari.readvec(file)
    if len(data) == 2:
        (F, Phi) = data
        R = PolynomialRing(QQ, str(F.variable()))
        A = FiniteFlatAlgebra(QQ, map(R, F))
        return DualPair(A, Phi.sage())
    elif len(data) == 3:
        (F, BF, Phi) = data
        R = PolynomialRing(QQ, str(F.variable()))
        A = FiniteFlatAlgebra(QQ, map(R, F), [M.sage() for M in BF])
        return DualPair(A, Phi.sage())
    else:
        (F, BF, G, BG, Phi) = data
        R = PolynomialRing(QQ, str(F.variable()))
        S = PolynomialRing(QQ, str(G.variable()))
        A = FiniteFlatAlgebra(QQ, map(R, F), [M.sage() for M in BF])
        B = FiniteFlatAlgebra(QQ, map(S, G), [M.sage() for M in BG])
        return DualPair(A, B, Phi.sage())
