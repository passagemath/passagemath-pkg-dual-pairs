# -*- coding: utf-8 -*-
r"""
Construction of dual pairs from number fields with Galois group
contained in :math:`\mathrm{GL}_2(F)` for a finite field :math:`F`.
"""

from __future__ import absolute_import

from sage.groups.matrix_gps.linear import GL
from sage.libs.gap.libgap import libgap
from sage.rings.polynomial.polynomial_element import Polynomial

from .dual_pair_from_table import dual_pair_from_table

def dual_pair_from_sub_GL2_field(L, F):
    r"""
    Return a dual pair encoding a Galois representation.

    INPUT:

    - `L` -- either a Galois extension of :math:`\mathbf{Q}` or a
      polynomial over :math:`\mathbf{Q}`

    - `F` -- a finite field such that the Galois group of :math:`L`
      over :math:`\mathbf{Q}` can be embedded into
      :math:`\mathrm{GL}_2(F)`

    EXAMPLES::

        sage: from dual_pairs.dual_pair_from_sub_GL2_field import dual_pair_from_sub_GL2_field
        sage: R.<x> = QQ[]

    An example with Galois group :math:`S_3` over
    :math:`\mathbf{F}_2`::

        sage: f = x^3 - x - 1
        sage: dual_pair_from_sub_GL2_field(f.splitting_field('a'), GF(2))
        [Dual pair of algebras over Rational Field
         A = Finite flat algebra of degree 4 over Rational Field, product of:
         Number Field in a0 with defining polynomial x
         Number Field in a1 with defining polynomial x^3 - x^2 + 1
         B = Finite flat algebra of degree 4 over Rational Field, product of:
         Number Field in a0 with defining polynomial x
         Number Field in a1 with defining polynomial x^3 - x^2 + 1]

    An example with Galois group :math:`Q_8` over
    :math:`\mathbf{F}_3`::

        sage: f = x^8 - 12*x^6 + 36*x^4 - 36*x^2 + 9
        sage: dual_pair_from_sub_GL2_field(f, GF(3))
        [Dual pair of algebras over Rational Field
         A = Finite flat algebra of degree 9 over Rational Field, product of:
         Number Field in a0 with defining polynomial x
         Number Field in a1 with defining polynomial x^8 - 12*x^6 + 36*x^4 - 36*x^2 + 9
         B = Finite flat algebra of degree 9 over Rational Field, product of:
         Number Field in a0 with defining polynomial x
         Number Field in a1 with defining polynomial x^8 + 12*x^6 + 36*x^4 + 36*x^2 + 9]

    An example with Galois group :math:`D_4` over :math:`\mathbf{F}_3`
    (cf. Serre, Divisibilité de certaines fonctions arithmétiques,
    exemple (4.4))::

        sage: dual_pair_from_sub_GL2_field(x^4 - 12, GF(3))
        [Dual pair of algebras over Rational Field
         A = Finite flat algebra of degree 9 over Rational Field, product of:
         Number Field in a0 with defining polynomial x
         Number Field in a1 with defining polynomial x^4 - 2*x^3 - 2*x + 1
         Number Field in a2 with defining polynomial x^4 - 3*x^2 + 3
         B = Finite flat algebra of degree 9 over Rational Field, product of:
         Number Field in a0 with defining polynomial x
         Number Field in a1 with defining polynomial x^4 - 2*x^3 - 2*x + 1
         Number Field in a2 with defining polynomial x^4 - 3*x^2 + 3]
    """
    AHC = libgap.function_factory('AllHomomorphismClasses')

    if isinstance(L, Polynomial):
        L = L.splitting_field('w')

    G = L.galois_group()
    inclusions = [f for f in AHC(G, GL(2, F)) if f.IsInjective()]
    return [dual_pair_from_table(G, F**2,
                                 {g: f.ImageElm(g)._matrix_(F) for g in G})
            for f in inclusions]
