# -*- coding: utf-8 -*-
"""
Constructing dual pairs from dihedral number fields
"""

from __future__ import absolute_import

from sage.groups.perm_gps.permgroup_named import DihedralGroup
from sage.matrix.constructor import matrix
from sage.rings.polynomial.polynomial_element import Polynomial

from .dual_pair_from_table import dual_pair_from_table

def dual_pair_from_dihedral_field(L, F):
    r"""
    Return a dual pair encoding a dihedral Galois representation.

    INPUT:

    - `L` -- either a Galois extension of :math:`\mathbf{Q}` with
      dihedral Galois group, or a polynomial over :math:`\mathbf{Q}`
      whose splitting field is such an extension

    - `F` -- a finite field such that the Galois group of `L` over
      :math:`\mathbf{Q}` can be embedded into :math:`\mathrm{GL}_2(F)`

    EXAMPLES::

        sage: from dual_pairs.dual_pair_from_dihedral_field import dual_pair_from_dihedral_field
        sage: R.<x> = QQ[]

    An example of level 23 over :math:`\mathbf{F}_2`::

        sage: f = x^3 - x - 1
        sage: dual_pair_from_dihedral_field(f.splitting_field('a'), GF(2))
        Dual pair of algebras over Rational Field
        A = Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^3 - x - 1
        B = Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^3 - x - 1

    An example of level 13 over :math:`\mathbf{F}_3`::

        sage: f = x^4 + x^2 - 3
        sage: L = f.splitting_field('w')
        sage: dual_pair_from_dihedral_field(L, GF(3))
        Dual pair of algebras over Rational Field
        A = Finite flat algebra of degree 9 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^4 - x^3 - x^2 - x + 1
        Number Field in a2 with defining polynomial x^4 + 2*x^2 - 3*x + 1
        B = Finite flat algebra of degree 9 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^4 - x^3 - x^2 - x + 1
        Number Field in a2 with defining polynomial x^4 + 2*x^2 - 3*x + 1

    An example of level 16 over :math:`\mathbf{F}_3` (cf. Serre,
    Divisibilité de certaines fonctions arithmétiques, exemple (4.4))::

        sage: dual_pair_from_dihedral_field(x^4 - 12, GF(3))
        Dual pair of algebras over Rational Field
        A = Finite flat algebra of degree 9 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^4 - 2*x^3 - 2*x + 1
        Number Field in a2 with defining polynomial x^4 - 3*x^2 + 3
        B = Finite flat algebra of degree 9 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^4 - 2*x^3 - 2*x + 1
        Number Field in a2 with defining polynomial x^4 - 3*x^2 + 3

    An example of level 23 over :math:`\mathbf{F}_5`::

        sage: dual_pair_from_dihedral_field(x^3 - x - 1, GF(5))
        Dual pair of algebras over Rational Field
        A = Finite flat algebra of degree 25 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^3 - x - 1
        Number Field in a2 with defining polynomial x^3 - x - 1
        Number Field in a3 with defining polynomial x^3 - x - 1
        Number Field in a4 with defining polynomial x^6 + 3*x^5 + 19*x^4 + 31*x^3 + 121*x^2 + 143*x + 307
        Number Field in a5 with defining polynomial x^6 + 3*x^5 + 19*x^4 + 31*x^3 + 121*x^2 + 143*x + 307
        Number Field in a6 with defining polynomial x^3 - x - 1
        B = Finite flat algebra of degree 25 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x^12 - 6*x^11 + 20*x^10 - 34*x^9 + 69*x^8 - 84*x^7 + 440*x^6 - 186*x^5 + 196*x^4 + 1400*x^3 + 1110*x^2 - 1600*x + 4105
        Number Field in a2 with defining polynomial x^12 + 128*x^11 + 7561*x^10 + 266074*x^9 + 6149384*x^8 + 97619882*x^7 + 1087374619*x^6 + 8445691276*x^5 + 43165980311*x^4 + 117455115180*x^3 - 49919785310*x^2 - 1428330707300*x - 2669533475975
    """
    if isinstance(L, Polynomial):
        L = L.splitting_field('w')

    n = L.degree() // 2
    Dn = DihedralGroup(n)
    rho, sigma = Dn.gens()

    G = L.galois_group()
    if False:
        isom = Dn.isomorphism_to(G)
        rho = isom(rho)  # BUG: raises an error
        sigma = isom(sigma)
    else:
        isom = G.isomorphism_to(Dn)
        rho = [tau for tau in G if isom(tau) == rho][0]
        sigma = [tau for tau in G if isom(tau) == sigma][0]
    assert rho.order() == n and sigma.order() == 2 and (rho * sigma).order() == 2

    q = F.cardinality()
    if n.divides(q - 1):
        # split case
        z = F.zeta(n)
        im_rho = matrix(F, [[z, 0], [0, ~z]])
        im_sigma = matrix(F, [[0, 1], [1, 0]])
    elif n.divides(q + 1):
        # non-split case
        F2 = F.extension(2, 'a')
        z = F2.zeta(n)
        # TODO: the following probably fails if F is not a prime field
        t = F(z + z**q)
        im_rho = matrix(F, [[0, -1], [1, t]])
        im_sigma = matrix(F, [[0, 1], [1, 0]])

    table = { sigma**i * rho**j : im_sigma**i * im_rho**j
              for i in range(2) for j in range(n) }

    return dual_pair_from_table(G, F**2, table)
