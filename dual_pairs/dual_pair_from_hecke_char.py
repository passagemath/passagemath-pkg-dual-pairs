# -*- coding: utf-8 -*-
"""
Construction of dual pairs from Hecke characters.
"""

from sage.groups.perm_gps.all import CyclicPermutationGroup
from sage.libs.pari import pari
from sage.matrix.constructor import matrix
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ

from dual_pairs.dual_pair_from_table import dual_pair_from_table

# K: quadratic field
# m: modulus of K
# F: finite field
# chi: Hecke character of K with modulus m and values in F
def hecke_char_ff_to_galois_char(K, m, F, chi):
    Kp = K.pari_bnf()
    Kr = Kp.bnrinit(m)
    poly = Kr.bnrclassfield(flag=2).nfsplitting()
    R = PolynomialRing(QQ, 'x')
    M = QQ.extension(R(poly), 'b')
    incl = K.Hom(M)[0]

    M_pari = M.__pari__()

    G = M.galois_group()

    # work around https://github.com/sagemath/cypari2/issues/136
    # idealfrobenius(K, G, P) = K.idealfrobenius(G, P)
    idealfrobenius = pari('(K,G,P)->Vecsmall(Vec(idealfrobenius(K,G,P)))')

    # Frobenius element (in G) attached to a prime p of K that is
    # unramified in L (and M)
    def frobenius(p):
        f = p.residue_class_degree()
        # transfer p to an ideal of M
        p = M.fractional_ideal([incl(x) for x in p.gens()])
        P = M_pari.idealfactor(p)[0, 0]
        return G(idealfrobenius(M_pari, G._pari_data, P)) ** f

    # TODO: remove hardcoded bound
    S = [p for p in K.primes_of_bounded_norm(100)
         if p.is_coprime(M.absolute_discriminant())]

    H = G.subgroup([frobenius(p) for p in S])
    assert H.is_abelian() and H.order() == M.degree() / 2

    q = F.order()
    g = F.multiplicative_generator()

    C = CyclicPermutationGroup(q - 1)
    c = C.gen()
    phi = H.hom([c ** (chi(p).log(g)) for p in S])
    logs = {c**i: i for i in range(q - 1)}

    return G, H, {h: matrix(F, [[g ** logs[phi(h)]]]) for h in H}

def hecke_char_to_galois_char(K, m, chi, P):
    F = P.residue_field()
    return hecke_char_ff_to_galois_char(K, P * m, F, lambda b: F(chi(b)))

def induced_representation(G, H, table, descend=False):
    zero = 0 * table[H.one()]
    F = zero.base_ring()
    # coset representatives for H\G
    R = [x[0] for x in G.cosets(H, side='left')]

    def block(g, r, s):
        h = r * g * ~s
        return table[h] if h in H else zero

    def rho(g):
        return matrix.block(F, [[block(g, r, s) for s in R] for r in R])

    table2 = {g: rho(g) for g in G}

    if descend:
        o = max(table[h][0, 0].multiplicative_order() for h in H)
        h0 = next(h for h in H if table[h][0, 0].multiplicative_order() == o)
        a, b = table2[h0].diagonal()
        r = next(r for r in R if r not in H)
        c = table2[r][1, 0].sqrt()
        P = matrix(F, [[1, a], [c, b*c]])
        Q = ~P
        F = F.base_ring()
        table2 = {g: (Q * table2[g] * P).change_ring(F) for g in G}

    return F ** 2, table2

def dual_pair_from_hecke_char(K, m, chi, P, descend=False):
    G, H, table = hecke_char_to_galois_char(K, m, chi, P)
    V, table2 = induced_representation(G, H, table, descend=descend)
    return dual_pair_from_table(G, V, table2)
