# -*- coding: utf-8 -*-
r"""
Conversion of finite flat algebras to étale algebras over
:math:`\mathbf{Q}.
"""

from __future__ import absolute_import

from sage.categories.algebras import Algebras
from sage.categories.cartesian_product import cartesian_product
from sage.categories.morphism import SetMorphism
from sage.matrix.constructor import Matrix
from sage.libs.pari import pari
from sage.misc.all import prod
from sage.misc.cachefunc import cached_function
from sage.modules.free_module_element import vector
from sage.rings.integer_ring import ZZ
from sage.rings.number_field.number_field import NumberField
from sage.rings.rational_field import QQ

from .finite_flat_algebra import FiniteFlatAlgebra

def _concat_vectors(v):
    return vector(sum((list(b) for b in v), []))

def isom_to_number_field(A):
    """
    Return an isomorphism from `A` to a number field.

    INPUT:

    - `A` -- a :class:`FiniteFlatAlgebra` over `QQ` that is a field

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: from dual_pairs.etale_algebra import isom_to_number_field
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, x)
        sage: isom_to_number_field(A)
        (Ring morphism:
           From: Number Field in a with defining polynomial x - 1
           To:   Monogenic algebra of degree 1 over Rational Field with defining polynomial x
           Defn: 1 |--> 1,
         Ring morphism:
           From: Monogenic algebra of degree 1 over Rational Field with defining polynomial x
           To:   Number Field in a with defining polynomial x - 1
           Defn: 1 |--> 1)
    """
    n = A.degree()
    for b in A.basis():
        f = b.matrix().minpoly()
        if f.degree() == n:
            K = NumberField(f, names='a')
            from_K = K.hom([b])
            M = Matrix(K, [c.module_element() for c in b.powers(n)])
            to_K = A.hom(M.inverse().rows(), K)
            return from_K, to_K
    raise NotImplementedError('no basis element of the right degree')

# TODO: make into a cached method of FiniteFlatAlgebra?
@cached_function
def isom_to_etale_algebra(A):
    """
    Return an isomorphism from `A` to a product of number fields.

    INPUT:

    - `A` -- a :class:`FiniteFlatAlgebra` over `QQ`

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: from dual_pairs.etale_algebra import isom_to_etale_algebra
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x^2 + 23])
        sage: isom_to_etale_algebra(A)
        (Ring morphism:
           From: Finite flat algebra of degree 3 over Rational Field, product of:
         Number Field in a0 with defining polynomial x
         Number Field in a1 with defining polynomial x^2 + 23
           To:   The Cartesian product of (Number Field in a with defining polynomial x - 1, Number Field in a with defining polynomial x^2 + 23)
           Defn: (1, 0) |--> (1, 0)
                 (0, 1) |--> (0, 1)
                 (0, a1) |--> (0, a),
         Generic morphism:
           From: The Cartesian product of (Number Field in a with defining polynomial x - 1, Number Field in a with defining polynomial x^2 + 23)
           To:   Finite flat algebra of degree 3 over Rational Field, product of:
         Number Field in a0 with defining polynomial x
         Number Field in a1 with defining polynomial x^2 + 23)
    """
    if A.base_ring() is not QQ:
        raise NotImplementedError('only implemented for dual pairs over QQ')

    Af = A.finite_dimensional_algebra()
    fields = []
    images = []
    matrices = []
    from_maps = []

    for p in Af.primary_decomposition():
        Kf = p.codomain()
        Mp = p.matrix()
        Ka = FiniteFlatAlgebra(QQ, Kf.table())
        from_K, to_K = isom_to_number_field(Ka)
        fields.append(from_K.domain())
        images.append([to_K(x.module_element() * Mp) for x in A.basis()])
        matrices.append(Mp)
        from_maps.append(from_K)

    category = Algebras(QQ).Commutative().CartesianProducts()

    P = cartesian_product(fields, category=category)

    # to_P = A.hom(list(zip(*images)), P)
    to_P = A.hom([P(x) for x in zip(*images)], P, check=False)

    inverse_matrix = Matrix.block(matrices, nrows=1).inverse()

    def inverse(x):
        v = [f(a).module_element() for f, a in zip(from_maps, x)]
        return A(_concat_vectors(v) * inverse_matrix)

    from_P = SetMorphism(P.Hom(A), inverse)

    # random consistency check
    u = A.random_element()
    v = to_P(u)
    assert from_P(v) == u
    v = P([K.random_element() for K in fields])
    u = from_P(v)
    assert to_P(u) == v

    return to_P, from_P

def nth_root(A, x, n):
    """
    Return an `n`-th root of `x` in `A`.
    """
    to_P, from_P = isom_to_etale_algebra(A)
    return from_P([y.nth_root(n) for y in to_P(x)])

@cached_function
def ideal_monoid(A):
    to_P, from_P = isom_to_etale_algebra(A)
    P = from_P.domain()
    factors = P.cartesian_factors()
    return cartesian_product([K.ideal_monoid() for K in factors])

def principal_ideal(A, x):
    to_P, from_P = isom_to_etale_algebra(A)
    P = from_P.domain()
    factors = P.cartesian_factors()
    PI = ideal_monoid(A)
    return PI([K.ideal(y) for K, y in zip(factors, to_P(x))])

# see NumberField_generic.selmer_generators()
def _ideal_generator(K, S, I):
    if not I.is_principal():
        H = K.class_group()
        gen_ords = [g.order() for g in H.gens()]
        pari_ords = pari(gen_ords).Col()
        MS = Matrix(ZZ, [H(s).exponents() for s in S]).transpose()
        pari_MS = pari(MS)
        B = H(I).exponents()
        pari_B = -pari(B).Col()
        exps = pari_MS.matsolvemod(pari_ords, pari_B).sage()
        Spart = prod(p ** e for p, e in zip(S, exps))
        I = I * Spart
    assert I.is_principal()
    return I.gens_reduced()[0]

def ideal_generator(A, S, I):
    S_prod = prod(S)
    to_P, from_P = isom_to_etale_algebra(A)
    P = from_P.domain()
    factors = P.cartesian_factors()
    return from_P([_ideal_generator(K, K.primes_above(S_prod), J)
                   for K, J in zip(factors, I)])

def _ideal_is_generator(K, S, I, x):
    return all(P in S for P in (I/x).support())

def ideal_is_generator(A, S, I, x):
    S_prod = prod(S)
    to_P, from_P = isom_to_etale_algebra(A)
    P = from_P.domain()
    factors = P.cartesian_factors()
    return all(_ideal_is_generator(K, K.primes_above(S_prod), J, y)
               for K, J, y in zip(factors, I, to_P(x)))

def map_ideal(f, I):
    # f: A -> B morphism of finite flat algebras
    # I in the ideal monoid of A
    A = f.domain()
    B = f.codomain()
    to_P, from_P = isom_to_etale_algebra(A)
    to_Q, from_Q = isom_to_etale_algebra(B)
    QI = ideal_monoid(B)
    gens = (J.gens_two() for J in I)
    u, v = [to_Q(f(from_P(x))) for x in zip(*gens)]
    return QI(zip(u, v))

def _ideal_root(K, S, I, n):
    f = pari('(K,A,n)->if(idealispower(K,A,n,&B),B,error("not a power"))')
    J = I * prod(p ** -I.valuation(p) for p in S)
    return K.ideal(f(K, J, n))

def ideal_root(A, S, I, n):
    S_prod = prod(S)
    to_P, from_P = isom_to_etale_algebra(A)
    P = from_P.domain()
    factors = P.cartesian_factors()
    PI = ideal_monoid(A)
    return PI([_ideal_root(K, K.primes_above(S_prod), J, n)
               for K, J in zip(factors, I)])
