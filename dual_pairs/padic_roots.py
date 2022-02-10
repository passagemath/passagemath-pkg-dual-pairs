# -*- coding: utf-8 -*-
"""
Utility functions for `p`-adic roots
"""

from sage.rings.all import PolynomialRing

def reduce_element(a, K):
    """
    TODO
    """
    k = K.residue_field()
    if K.degree() == 1:
        # K = Q_p
        return k(a)
    elif K(a).valuation() > 0:
        return k.zero()
    elif K.gen().valuation() > 0:
        # Eisenstein polynomial
        return k(K(a).expansion()[0])
    else:
        return k(K(a).expansion())

def reduce_poly(f, K):
    """
    TODO
    """
    k = K.residue_field()
    x = f.variable_name()
    R = PolynomialRing(k, x)
    return R([reduce_element(a, K) for a in f.list()])

def roots_mod_m(f, K):
    """
    TODO
    """
    return reduce_poly(f, K).roots(multiplicities=False)

def lift_root(f, a, K):
    """
    TODO
    """
    # assume f'(a) is a unit
    a = K(a)
    g = f.derivative()
    if g(a).valuation() != 0:
        raise ValueError('%s is not a simple root of %s' % (a, f))
    while f(a) != 0:
        a -= f(a)/g(a)
    return a

def rootpadic(f, a, K):
    """
    Return the roots of `f` in `K` that are congruent to `a` modulo
    the maximal ideal.
    """
    # print('looking at a = %s' % a)
    a = K(a)
    if f.derivative()(a).valuation() == 0:
        return [lift_root(f, a, K)]
    x = f.parent().gen()
    pi = K.uniformiser()
    g = f(pi * x + a) / pi
    v = min(c.valuation() for c in g.coefficients(sparse=True))
    g = g / pi**v
    r = roots_mod_m(g, K)
    # print('roots of %s mod m: %s' % (g, r))
    return sum(([pi * u + a for u in rootpadic(g, b.lift(), K)]
                for b in r), [])

# assume f has integral coefficients and is squarefree
def padic_roots(f, K):
    """
    Return the roots of `f` in the `p`-adic field `K`.

    TESTS::

        sage: from dual_pairs.padic_roots import padic_roots
        sage: R.<x> = PolynomialRing(QQ)
        sage: K.<a> = Qp(23, 20).extension(x^2 + 23)
        sage: padic_roots(x, K)
        [0]
        sage: padic_roots(x^3 - x - 1, K)
        [3 + 8*a^2 + 18*a^4 + 21*a^8 + 2*a^10 + 21*a^12 + 2*a^16 + 17*a^18 + 10*a^20 + 10*a^22 + 20*a^24 + 18*a^26 + 22*a^28 + 18*a^30 + 18*a^32 + 16*a^34 + 21*a^36 + 8*a^38 + O(a^40),
         10 + 19*a + 8*a^2 + 19*a^3 + 3*a^4 + 18*a^5 + 12*a^6 + a^7 + 13*a^8 + 7*a^9 + 6*a^11 + a^12 + 5*a^13 + 12*a^14 + 7*a^15 + 11*a^16 + 15*a^17 + 15*a^18 + 12*a^19 + 19*a^20 + 16*a^21 + 19*a^22 + 18*a^23 + 14*a^24 + 19*a^25 + 15*a^26 + 4*a^27 + 13*a^28 + a^29 + 15*a^30 + 20*a^31 + 15*a^32 + 7*a^33 + 16*a^34 + 12*a^35 + 2*a^36 + 8*a^38 + O(a^39),
         10 + 4*a + 8*a^2 + 5*a^3 + 3*a^4 + 6*a^5 + 12*a^6 + 13*a^8 + 16*a^9 + 18*a^11 + a^12 + 19*a^13 + 12*a^14 + 17*a^15 + 11*a^16 + 9*a^17 + 15*a^18 + 12*a^19 + 19*a^20 + 8*a^21 + 19*a^22 + 6*a^23 + 14*a^24 + 5*a^25 + 15*a^26 + 20*a^27 + 13*a^28 + 15*a^30 + 3*a^31 + 15*a^32 + 17*a^33 + 16*a^34 + 12*a^35 + 2*a^36 + a^37 + 8*a^38 + O(a^39)]
        sage: padic_roots(x^6 - 6*x^4 + 9*x^2 + 23, K)
        [15*a + 14*a^3 + 12*a^5 + a^7 + 14*a^9 + 12*a^11 + 10*a^13 + 14*a^15 + 7*a^17 + 8*a^21 + 12*a^23 + 14*a^25 + 7*a^27 + 2*a^29 + 17*a^31 + 13*a^33 + a^35 + 22*a^37 + 16*a^39 + O(a^41),
         8*a + 10*a^3 + 12*a^5 + 9*a^9 + 12*a^11 + 14*a^13 + 10*a^15 + 17*a^17 + a^19 + 15*a^21 + 12*a^23 + 10*a^25 + 17*a^27 + 22*a^29 + 7*a^31 + 11*a^33 + a^37 + 8*a^39 + O(a^41),
         16 + 19*a + a^2 + 19*a^3 + 15*a^4 + 18*a^5 + 11*a^6 + a^7 + 9*a^8 + 7*a^9 + 2*a^10 + 6*a^11 + 20*a^12 + 5*a^13 + 11*a^14 + 7*a^15 + 15*a^16 + 15*a^17 + 3*a^18 + 12*a^19 + 14*a^20 + 16*a^21 + 15*a^22 + 18*a^23 + 7*a^24 + 19*a^25 + 3*a^26 + 4*a^27 + 9*a^28 + a^29 + 3*a^30 + 20*a^31 + 3*a^32 + 7*a^33 + 12*a^35 + 19*a^36 + O(a^39),
         16 + 4*a + a^2 + 5*a^3 + 15*a^4 + 6*a^5 + 11*a^6 + 9*a^8 + 16*a^9 + 2*a^10 + 18*a^11 + 20*a^12 + 19*a^13 + 11*a^14 + 17*a^15 + 15*a^16 + 9*a^17 + 3*a^18 + 12*a^19 + 14*a^20 + 8*a^21 + 15*a^22 + 6*a^23 + 7*a^24 + 5*a^25 + 3*a^26 + 20*a^27 + 9*a^28 + 3*a^30 + 3*a^31 + 3*a^32 + 17*a^33 + 12*a^35 + 19*a^36 + a^37 + O(a^39),
         7 + 19*a + 19*a^3 + 8*a^4 + 18*a^5 + 13*a^6 + a^7 + 15*a^8 + 7*a^9 + 22*a^10 + 6*a^11 + 4*a^12 + 5*a^13 + 13*a^14 + 7*a^15 + 9*a^16 + 15*a^17 + 21*a^18 + 12*a^19 + 10*a^20 + 16*a^21 + 9*a^22 + 18*a^23 + 17*a^24 + 19*a^25 + 21*a^26 + 4*a^27 + 15*a^28 + a^29 + 21*a^30 + 20*a^31 + 21*a^32 + 7*a^33 + a^34 + 12*a^35 + 4*a^36 + a^38 + O(a^39),
         7 + 4*a + 5*a^3 + 8*a^4 + 6*a^5 + 13*a^6 + 15*a^8 + 16*a^9 + 22*a^10 + 18*a^11 + 4*a^12 + 19*a^13 + 13*a^14 + 17*a^15 + 9*a^16 + 9*a^17 + 21*a^18 + 12*a^19 + 10*a^20 + 8*a^21 + 9*a^22 + 6*a^23 + 17*a^24 + 5*a^25 + 21*a^26 + 20*a^27 + 15*a^28 + 21*a^30 + 3*a^31 + 21*a^32 + 17*a^33 + a^34 + 12*a^35 + 4*a^36 + a^37 + a^38 + O(a^39)]
    """
    r = roots_mod_m(f, K)
    # print('roots of %s mod m: %s' % (f, r))
    R = sum((rootpadic(f, a.lift(), K) for a in r), [])
    assert all(f(a) == 0 for a in R)
    return R

def kummer_dedekind(f):
    """
    TODO
    """
    K = f.base_ring()
    x = f.parent().gen()
    if f.degree() == 1:
        return x
    r = roots_mod_m(f, K)
    if len(r) == 0:
        return f
    assert len(r) == 1
    a = r[0].lift()
    f = f(x + a)
    if f(0).valuation() == 1:
        return f
    p = K.prime()
    if f.degree() == 2:
        return kummer_dedekind(f(p*x)/p^2)
    raise NotImplementedError('maximal order of %s-adic field defined by %s'
                              % (p, f))

def integral_basis_generator(f):
    """
    TODO
    """
    try:
        return kummer_dedekind(f)
    except NotImplementedError:
        pass
    from sage.libs.pari import pari
    p = f.base_ring().prime()
    f = f.lift()
    R = f.parent()
    # Note: the nfbasis method in cypari2 has a different convention
    # for the arguments than the nfbasis function in PARI.
    basis = pari(f).nfbasis(0, [p])
    for b in basis:
        g = R(b.Mod(f).minpoly())
        if g(0).valuation(p) == 1:
            # Eisenstein polynomial
            return g
    raise NotImplementedError('maximal order of %s-adic field defined by %s'
                              % (p, f))

def padic_aut(K, r):
    """
    Return a map that sends an element of K to its image
    under the automorphism that maps K.gen() to r.

    TESTS::

        sage: from dual_pairs.padic_roots import padic_aut
        sage: R.<x> = QQ[]
        sage: K.<a> = Qp(23).extension(x^2 + 23)
        sage: padic_aut(K, -a)(a)
        22*a + a^3 + O(a^41)
        sage: padic_aut(K, -a)(a^2 + 4*a - 5) == a^2 - 4*a - 5
        True
    """
    # TODO: this is a horrible hack
    from sage.categories.morphism import SetMorphism
    from sage.libs.pari import pari
    Qp = K.base_ring()
    R = PolynomialRing(Qp, 'x')
    return SetMorphism(K.Hom(K), lambda x: R(pari(x).Pol())(r))
