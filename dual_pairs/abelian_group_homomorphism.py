# -*- coding: utf-8 -*-
"""
Homomorphisms between finite Abelian groups.
"""

from __future__ import absolute_import

from sage.categories.morphism import Morphism
from sage.groups.abelian_gps.abelian_group import AbelianGroup
from sage.matrix.constructor import Matrix
from sage.misc.cachefunc import cached_method
from sage.modules.free_module_element import vector
from sage.rings.integer_ring import ZZ
from sage.structure.richcmp import richcmp

def solve_mod(M, N, D):
    """
    Return an integral solution of ``X * M == N (mod D)``.

    EXAMPLES::

        sage: from dual_pairs.abelian_group_homomorphism import solve_mod
        sage: M = Matrix([(-1, -1, 0, -1, 0, 1, 0, 1, 0, 0),
        ....:             (-1, -1, 0, -1, 0, 1, 0, 0, 0, 0),
        ....:             (0, 0, 0, 0, 0, 0, 1, 0, -1, 0)])
        sage: N = Matrix([(1, 1, 0, 1, 0, 1, 0, 0, 0, 0),
        ....:             (0, 0, 0, 0, 0, 0, 0, 1, 0, 0),
        ....:             (0, 0, 0, 0, 0, 0, 2, 0, -2, 0)])
        sage: D = vector([2, 2, 0, 2, 0, 2, 0, 2, 0, 0])
        sage: solve_mod(M, N, D)
        [0 1 0]
        [1 1 0]
        [0 0 2]
    """
    Mp = M.__pari__().mattranspose()
    Np = N.__pari__().mattranspose()
    Dp = D.__pari__().Col()
    return Matrix(ZZ, N.nrows(), M.nrows(),
                  [Mp.matsolvemod(Dp, v).sage() for v in Np])

def solve_mod_right(M, N, D):
    """
    Return an integral solution of ``M * X == N (mod D)``.

    EXAMPLES::

        sage: from dual_pairs.abelian_group_homomorphism import solve_mod_right
        sage: M = Matrix([(-1, -1, 0, -1),
        ....:             (0, 0, 0, 0)])
        sage: N = Matrix([(1, 1, 0, 1),
        ....:             (0, 0, 0, 0)])
        sage: D = vector([2, 0])
        sage: solve_mod_right(M, N, D)
        [ 0  0  0  0]
        [-1 -1  0 -1]
        [ 0  0  0  0]
        [ 0  0  0  0]
    """
    Mp = M.__pari__()
    Np = N.__pari__()
    Dp = D.__pari__().Col()
    return Matrix(ZZ, N.ncols(), M.ncols(),
                  [Mp.matsolvemod(Dp, v).sage() for v in Np]).transpose()

def relation_matrix(A):
    R = Matrix.diagonal(A.gens_orders())
    return Matrix([r for r in R.rows() if r])

# TODO: AbelianGroup_class.element_class should do the reduction
# modulo the orders!
def _normalise(A, x):
    return A([e % o if o else e
              for e, o in zip(A(x).exponents(), A.gens_orders())])

class AbelianGroupHomomorphism(Morphism):
    """
    A homomorphism between finitely generated Abelian groups.
    """

    def __init__(self, parent, im_gens):
        """
        Initialise ``self``.

        INPUT:

        - ``parent`` -- homset of finitely generated Abelian groups

        - ``im_gens`` -- list of elements defining a group
          homomorphism
        """
        A = parent.domain()
        B = parent.codomain()
        RA = relation_matrix(A)
        RB = relation_matrix(B)
        im_gens = tuple(_normalise(B, x) for x in im_gens)
        self._im_gens = im_gens
        self._M = Matrix(ZZ, A.ngens(), B.ngens(),
                         [x.exponents() for x in im_gens])
        self._N = RB.solve_left(RA * self._M).change_ring(ZZ)
        Morphism.__init__(self, parent)

    def im_gens(self):
        return self._im_gens

    # TODO: AbelianGroup_class.element_class should implement
    # _im_gens_!
    def _call_(self, x):
        y = vector(ZZ, x.exponents()) * self.matrix()
        return _normalise(self.codomain(), y)

    def _composition_(self, right, homset):
        im_gens = [self(x) for x in right.im_gens()]
        return AbelianGroupHomomorphism(homset, im_gens)

    def _richcmp_(self, other, op):
        return richcmp(self.im_gens(), other.im_gens(), op)

    def _repr_type(self):
        return "Abelian group"

    def _repr_(self):
        """
        Return a string representation of ``self``.

        EXAMPLES::

            sage: from dual_pairs.abelian_group_homomorphism import hom
            sage: A = AbelianGroup([2, 2, 0])
            sage: B = AbelianGroup([2, 2, 0, 2, 0, 2, 0, 2, 0, 0])
            sage: im_gens = (B([1, 1, 0, 1, 0, 1, 0, 0, 0, 0]),
            ....:            B([0, 0, 0, 0, 0, 0, 0, 1, 0, 0]),
            ....:            B([0, 0, 0, 0, 0, 0, 2, 0, -2, 0]))
            sage: hom(A, B, im_gens)
            Abelian group morphism:
              From: Multiplicative Abelian group isomorphic to C2 x C2 x Z
              To:   Multiplicative Abelian group isomorphic to C2 x C2 x Z x C2 x Z x C2 x Z x C2 x Z x Z
            Defn:
              f0 |--> f0*f1*f3*f5
              f1 |--> f7
              f2 |--> f6^2*f8^-2
        """
        s = '\n'.join('  {} |--> {}'.format(g, x)
                      for g, x in zip(self.domain().gens(), self.im_gens()))
        return Morphism._repr_(self) + '\nDefn:\n' + s

    def is_trivial(self):
        return all(x.is_one() for x in self._im_gens)

    def matrix(self):
        return self._M

    @cached_method
    def kernel(self):
        """
        Return the kernel of ``self``.

        OUTPUT:

        The kernel of ``self`` as an Abelian group `K` (given by Smith
        normal form generators) together with an injective
        homomorphism from `K` to the domain of ``self``.

        EXAMPLES::

            sage: from dual_pairs.abelian_group_homomorphism import hom
            sage: A = AbelianGroup([2, 2, 0])
            sage: B = AbelianGroup([2, 2, 0, 2, 0, 2, 0, 2, 0, 0])
            sage: im_gens = (B([1, 1, 0, 1, 0, 1, 0, 0, 0, 0]),
            ....:            B([0, 0, 0, 0, 0, 0, 0, 1, 0, 0]),
            ....:            B([0, 0, 0, 0, 0, 0, 2, 0, -2, 0]))
            sage: hom(A, B, im_gens).kernel()
            Abelian group morphism:
              From: Trivial Abelian group
              To:   Multiplicative Abelian group isomorphic to C2 x C2 x Z
            Defn:
        """
        A = self.domain()
        B = self.codomain()
        RA = relation_matrix(A)
        RB = relation_matrix(B)
        E = self.matrix()
        L = E.stack(RB).integer_kernel().basis_matrix()
        M = L.submatrix(ncols=A.ngens())
        N = M.solve_left(RA).change_ring(ZZ)
        RK, U, V = N.smith_form()
        X = V.solve_right(M)
        # now RA = N*M, RK = U*N*V, RK*X = U*RA, M = V*X
        DK = RK.diagonal() + [0] * (RK.ncols() - RK.nrows())
        K = AbelianGroup([o for o in DK if o != 1])
        im_gens = [x for o, x in zip(DK, X.rows()) if o != 1]
        return hom(K, A, im_gens)

    @cached_method
    def cokernel(self):
        """
        Return the cokernel of ``self``.

        OUTPUT:

        The cokernel of ``self`` as an Abelian group `C` (given by
        Smith normal form generators) together with a surjective
        homomorphism from the codomain of ``self`` to `C`.

        EXAMPLES::

            sage: from dual_pairs.abelian_group_homomorphism import hom
            sage: A = AbelianGroup([2, 2, 0])
            sage: B = AbelianGroup([2, 2, 0, 2, 0, 2, 0, 2, 0, 0])
            sage: im_gens = (B([1, 1, 0, 1, 0, 1, 0, 0, 0, 0]),
            ....:            B([0, 0, 0, 0, 0, 0, 0, 1, 0, 0]),
            ....:            B([0, 0, 0, 0, 0, 0, 2, 0, -2, 0]))
            sage: hom(A, B, im_gens).cokernel()
            Abelian group morphism:
              From: Multiplicative Abelian group isomorphic to C2 x C2 x Z x C2 x Z x C2 x Z x C2 x Z x Z
              To:   Multiplicative Abelian group isomorphic to C2 x C2 x C2 x C2 x Z x Z x Z x Z
            Defn:
              f0 |--> f1*f2*f3
              f1 |--> f2
              f2 |--> f4
              f3 |--> f1
              f4 |--> f5
              f5 |--> f3
              f6 |--> f6
              f7 |--> 1
              f8 |--> f0*f6
              f9 |--> f7
        """
        B = self.codomain()
        RB = relation_matrix(B)
        M = self.matrix()
        H = Matrix(ZZ, [r for r in M.stack(RB).hermite_form().rows() if r],
                   ncols=B.ngens())
        RC, U, V = H.smith_form()
        DC = RC.diagonal() + [0] * (RC.ncols() - RC.nrows())
        C = AbelianGroup([o for o in DC if o != 1])
        W = Matrix(ZZ, C.ngens(), B.ngens(),
                   [V.column(i) for i, o in enumerate(DC) if o != 1]).transpose()
        return hom(B, C, W.rows())

    def inverse_image(self, x):
        """
        Return an inverse image of ``x`` under ``self``.

        EXAMPLES::

            sage: from dual_pairs.abelian_group_homomorphism import hom
            sage: A = AbelianGroup([2, 4, 0])
            sage: B = AbelianGroup([4, 8, 0])
            sage: im_gens = (B([2, 4, 0]),
            ....:            B([1, 2, 0]),
            ....:            B([0, 4, 2]))
            sage: h = hom(A, B, im_gens)
            sage: y = h(A.random_element())
            sage: h(h.inverse_image(y)) == y
            True
        """
        A = self.domain()
        B = self.codomain()
        RB = relation_matrix(B)
        M = self.matrix()
        E = -Matrix(ZZ, [x.exponents()])
        S = E.stack(M).stack(RB)
        K = S.integer_kernel().basis_matrix().hermite_form()
        r = K.row(0)
        if r[0] != 1:
            raise ValueError('{} is not in the image of {}'.format(x, self))
        return A(r[1:A.ngens()+1])

    def solve_right(self, h):
        """
        Return a solution `g` of `self * g == h`.

        TODO: this may not always work (maybe if self is injective?)
        """
        # self: B -> C
        # h: A -> C
        # g: A -> B
        C = self.codomain()
        if h.codomain() != C:
            raise ValueError("maps have different codomains")
        B = self.domain()
        A = h.domain()
        # TODO: is this enough???
        X = solve_mod(self.matrix(), h.matrix(), vector(C.gens_orders()))
        return hom(A, B, X)

    def solve_left(self, h):
        """
        Return a solution `g` of `g * self == h`.

        TODO: this is wrong; generalise inverse_image() instead
        """
        # self: A -> B
        # h: A -> C
        # g: B -> C
        A = self.domain()
        if h.domain() != A:
            raise ValueError("maps have different domains")
        B = self.codomain()
        C = h.codomain()
        X = solve_mod_right(self.matrix(), h.matrix(), vector(C.gens_orders()))
        return hom(B, C, X)

def hom(A, B, im_gens):
    # explicitly pass category because otherwise some morphisms end up
    # in the category of *finite* commutative groups
    from sage.categories.groups import Groups
    return AbelianGroupHomomorphism(A.Hom(B, category=Groups().Commutative()), im_gens)

def homology(f, g):
    """
    Return the homology group of the pair `(f, g)`.
    """
    ker_g = g.kernel()
    coker_f = f.cokernel()
    L = coker_f.codomain()
    fbar = ker_g.solve_right(f)
    h = coker_f * ker_g
    p = fbar.cokernel()
    H = p.codomain()
    i = hom(H, L, [h(p.inverse_image(x)) for x in H.gens()])
    return p, i
