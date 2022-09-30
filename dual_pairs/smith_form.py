# -*- coding: utf-8 -*-
r"""
Smith normal form for Abelian groups
"""

from __future__ import absolute_import

from sage.groups.abelian_gps.abelian_group import AbelianGroup
from sage.matrix.all import Matrix
from sage.misc.all import prod
from sage.modules.free_module_element import vector
from sage.rings.integer_ring import ZZ

def abelian_group_smith_form(R, one, gens_0, log_0):
    S, U, V = R.smith_form()
    D = S.diagonal()
    W = V.inverse_of_unit()
    orders = tuple(o for o in D if o != 1)
    rows_W1 = [x for o, x in zip(D, W.rows()) if o != 1]
    cols_V1 = [x for o, x in zip(D, V.columns()) if o != 1]
    V1 = Matrix(ZZ, len(orders), len(D), cols_V1).transpose()

    B = AbelianGroup(orders)
    gens = [prod((a ** i for a, i in zip(gens_0, x)), one) for x in rows_W1]

    def exp(x):
        return prod((a ** i for a, i in zip(gens, x.exponents())), one)

    def log(x):
        return B(vector(ZZ, log_0(x)) * V1)

    return B, gens, exp, log
