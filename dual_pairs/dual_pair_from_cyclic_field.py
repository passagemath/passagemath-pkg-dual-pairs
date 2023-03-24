# -*- coding: utf-8 -*-
"""
Constructing dual pairs from cyclic number fields
"""

from __future__ import absolute_import

from sage.groups.perm_gps.permgroup_named import CyclicPermutationGroup
from sage.matrix.constructor import matrix
from sage.rings.polynomial.polynomial_element import Polynomial

from .dual_pair_from_table import dual_pair_from_table

def dual_pair_from_cyclic_field(L, F):
    r"""
    Return a dual pair encoding a cyclic Galois representation.

    INPUT:

    - `L` -- either a cyclic extension of :math:`\mathbf{Q}`, or a
      polynomial over :math:`\mathbf{Q}` whose splitting field is such
      an extension

    - `F` -- a finite field such that the Galois group of `L` over
      :math:`\mathbf{Q}` can be embedded into :math:`\mathrm{GL}_2(F)`

    EXAMPLES::

        sage: from dual_pairs.dual_pair_from_cyclic_field import dual_pair_from_cyclic_field
        sage: R.<x> = QQ[]

    An example of level 7 over :math:`\mathbf{F}_2`::

        sage: f = x^3 - x^2 - 2*x + 1
        sage: dual_pair_from_cyclic_field(f.splitting_field('a'), GF(2))
    """
    if isinstance(L, Polynomial):
        L = L.splitting_field('w')

    n = L.degree()
    Cn = CyclicPermutationGroup(n)
    rho = Cn.gen()

    G = L.galois_group()
    isom = Cn.isomorphism_to(G)
    rho = isom(rho)

    q = F.cardinality()
    if n.divides(q - 1):
        # split case
        z = F.zeta(n)
        im_rho = matrix(F, [[z, 0], [0, ~z]])
    elif n.divides(q + 1):
        # non-split case
        F2 = F.extension(2, 'a')
        z = F2.zeta(n)
        # TODO: the following probably fails if F is not a prime field
        t = F(z + z**q)
        im_rho = matrix(F, [[0, -1], [1, t]])

    table = { rho**j : im_rho**j for j in range(n) }

    return dual_pair_from_table(G, F**2, table)
