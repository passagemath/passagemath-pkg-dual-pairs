# -*- coding: utf-8 -*-
r"""
Selmer groups of finite flat algebras
"""

from __future__ import absolute_import

from sage.matrix.all import Matrix
from sage.misc.all import prod

from .abelian_group_homomorphism import hom
from .class_group import class_group
from .etale_algebra import ideal_generator, ideal_root, principal_ideal
from .smith_form import abelian_group_smith_form
from .unit_group import unit_group

def selmer_group(A, S, n):
    """
    Return the `n`-Selmer group of `A` relative to `S`.

    This is a version for étale algebras of the method
    :meth:`NumberField.selmer_space`.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: from dual_pairs.selmer_group import selmer_group
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x^3 - x - 1])
        sage: S = [2, 23]
        sage: Sel, gens, exp_Sel, log_Sel = selmer_group(A, S, 2)
        sage: v = Sel.random_element()
        sage: log_Sel(exp_Sel(v)) == v
        True

        sage: A = FiniteFlatAlgebra(QQ, x^2 - x + 6)
        sage: Sel, gens, exp_Sel, log_Sel = selmer_group(A, [], 6)
        sage: Sel
        Multiplicative Abelian group isomorphic to C6
        sage: gens
        [3/64*a + 1/32]
        sage: log_Sel(gens[0])
        f
        sage: exp_Sel(Sel.gen(0))
        3/64*a + 1/32
    """
    U, gens_U, exp_U, log_U = unit_group(A, S)
    Cl, gens_Cl, exp_Cl, log_Cl = class_group(A, S)

    coker_n_U = hom(U, U, [x**n for x in U.gens()]).cokernel()
    U_mod_n = coker_n_U.codomain()

    ker_n_Cl = hom(Cl, Cl, [x**n for x in Cl.gens()]).kernel()
    Cl_n = ker_n_Cl.domain()

    gens_U_mod_n = [exp_U(coker_n_U.inverse_image(x))
                    for x in U_mod_n.gens()]
    gens_Cl_n = [ideal_generator(A, S, exp_Cl(ker_n_Cl(x)) ** d) ** (n // d)
                 for x, d in zip(Cl_n.gens(), Cl_n.gens_orders())]
    gens = gens_U_mod_n + gens_Cl_n

    def log(a):
        I = ideal_root(A, S, principal_ideal(A, a), n)
        v = ker_n_Cl.inverse_image(log_Cl(I)).exponents()
        b = prod((y ** -i for y, i in zip(gens_Cl_n, v)), a)
        J = ideal_root(A, S, principal_ideal(A, b), n)
        g = ideal_generator(A, S, J)
        c = b * g**-n
        u = coker_n_U(log_U(c)).exponents()
        return list(u) + list(v)

    R = Matrix.diagonal(U_mod_n.gens_orders() + Cl_n.gens_orders())
    return abelian_group_smith_form(R, A.one(), gens, log)
