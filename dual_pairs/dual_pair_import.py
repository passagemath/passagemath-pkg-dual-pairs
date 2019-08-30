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

def dual_pair_import(filename):
    """
    Import a dual pair of algebras from ``filename``.

    INPUT:

    - ``filename`` -- string: name of either a regular file or a
      resource of the ``dual_pairs`` package.

    EXAMPLES::

        sage: from dual_pairs.dual_pair_import import dual_pair_import
        sage: dual_pair_import('example_data/D4_mod_3.gp')
        Dual pair of algebras over Rational Field
        A = Finite flat algebra of degree 9 over Rational Field, product of:
        Number Field in a0 with defining polynomial t
        Number Field in a1 with defining polynomial t^4 + t^2 - 3
        Number Field in a2 with defining polynomial t^4 - 7*t^2 + 13
        B = Finite flat algebra of degree 9 over Rational Field, product of:
        Number Field in a0 with defining polynomial t
        Number Field in a1 with defining polynomial t^4 + t^2 - 3
        Number Field in a2 with defining polynomial t^4 - 7*t^2 + 13

    .. TODO::

        Document accepted file formats.
    """
    try:
        import io
        stream = io.open(filename, 'r')
    except IOError:
        import pkg_resources
        stream = pkg_resources.resource_stream(__name__, filename)
    data = [pari(L) for L in stream.readlines()]

    if len(data) == 2:
        (F, Phi) = data
        R = PolynomialRing(QQ, str(F.variable()))
        A = FiniteFlatAlgebra(QQ, [R(f) for f in F])
        return DualPair(A, Phi.sage())
    elif len(data) == 3:
        (F, BF, Phi) = data
        R = PolynomialRing(QQ, str(F.variable()))
        A = FiniteFlatAlgebra(QQ, [R(f) for f in F], [M.sage() for M in BF])
        return DualPair(A, Phi.sage())
    else:
        (F, BF, G, BG, Phi) = data
        R = PolynomialRing(QQ, str(F.variable()))
        S = PolynomialRing(QQ, str(G.variable()))
        A = FiniteFlatAlgebra(QQ, [R(f) for f in F], [M.sage() for M in BF])
        B = FiniteFlatAlgebra(QQ, [S(g) for g in G], [M.sage() for M in BG])
        return DualPair(A, B, Phi.sage())
