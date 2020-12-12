# -*- coding: utf-8 -*-
"""
Finite flat algebras.
"""

from __future__ import absolute_import

from sage.algebras.finite_dimensional_algebras.finite_dimensional_algebra \
    import FiniteDimensionalAlgebra
from sage.matrix.all import Matrix
import sage.matrix.matrix0
from sage.misc.all import cached_method
from sage.misc.fast_methods import WithEqualityById
from sage.rings.ring import CommutativeAlgebra
from sage.structure.factory import UniqueFactory

from .finite_flat_algebra_element import (FiniteFlatAlgebraElement_monogenic,
                                          FiniteFlatAlgebraElement_product,
                                          FiniteFlatAlgebraElement_generic)


class FiniteFlatAlgebra_base(WithEqualityById, CommutativeAlgebra):
    """
    A finite flat algebra over a ring.

    This is an abstract base class.

    .. TODO::

        This should be generalised to not necessarily free modules.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, x^3 - x - 1)
        sage: A.zero()
        0
        sage: A.one()
        1
        sage: B = FiniteFlatAlgebra(QQ, [x, x^2 - 5])
        sage: B.zero()
        (0, 0)
        sage: B.one()
        (1, 1)
        sage: C = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
        sage: C.zero()
        0
        sage: C.one()
        e0
    """

    def __init__(self, base_ring):
        """
        Initialise a finite flat algebra over ``base_ring``.

        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
            sage: A.has_coerce_map_from(A.base_ring())
            True
            sage: B = FiniteFlatAlgebra(QQ, [x, x^2 + 1])
            sage: B.has_coerce_map_from(B.base_ring())
            True
        """
        from sage.categories.all import Algebras
        category = Algebras(base_ring).Commutative().FiniteDimensional().WithBasis()
        super(FiniteFlatAlgebra_base, self).__init__(base_ring, category=category)

    @cached_method
    def module(self):
        """
        Return the underlying module of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: S.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
            sage: A.module()
            Vector space of dimension 4 over Rational Field
        """
        from sage.modules.free_module import FreeModule
        return FreeModule(self.base_ring(), self.degree())

    @cached_method
    def gen(self, i):
        """
        Return the `i`-th distinguished generator of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^3 - 27, [1, 3*x, 9*x^2])
            sage: A.gen(1)
            3*a
            sage: A.gens()
            (1, 3*a, 9*a^2)
            sage: B = FiniteFlatAlgebra(QQ, [x, x^2 - 4], [[1], [1, 2*x]])
            sage: B.gen(2)
            (0, 2*a1)
            sage: B.gens()
            ((1, 0), (0, 1), (0, 2*a1))
        """
        return self.element_class(self, self.module().gen(i))

    def ngens(self):
        """
        Return the number of distinguished generators of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^2 - 9, [1, 3*x])
            sage: A.ngens()
            2
            sage: B = FiniteFlatAlgebra(QQ, [x, x^2 - 4], [[1], [1, 2*x]])
            sage: B.ngens()
            3
        """
        return self.degree()

    def basis(self):
        """
        Return the distinguished basis of ``self``.

        This method is required by :class:`ModulesWithBasis`.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^3 - x - 1)
            sage: A.basis()
            (1, a, a^2)
            sage: B = FiniteFlatAlgebra(QQ, x^3 - x - 1, [1, x^2 - 1, x])
            sage: B.basis()
            (1, a^2 - 1, a)
            sage: C = FiniteFlatAlgebra(QQ, [x, x^2 - 5])
            sage: C.basis()
            ((1, 0), (0, 1), (0, a1))
            sage: D = FiniteFlatAlgebra(QQ, [x, x^3 - x - 1], [[1], [1, x^2 - 1, x]])
            sage: D.basis()
            ((1, 0), (0, 1), (0, a1^2 - 1), (0, a1))
        """
        return self.gens()

    @cached_method
    def _basis_matrix_inv(self):
        """
        Return the inverse of the matrix of the distinguished basis of
        ``self``.
        """
        return ~self._basis_matrix()

    def _coerce_map_from_(self, X):
        """
        Return a coercion map from `X` to ``self``, or ``None``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
            sage: A.coerce_map_from(A.module())
            Coercion map:
              From: Vector space of dimension 4 over Rational Field
              To:   Monogenic algebra of degree 4 over Rational Field with defining polynomial x^4 - 16

            sage: B = FiniteFlatAlgebra(QQ, [x, x^2 + 1])
            sage: B.coerce_map_from(B.module())
            Coercion map:
              From: Vector space of dimension 3 over Rational Field
              To:   Finite flat algebra of degree 3 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x^2 + 1
        """
        if X is self.module() or X is self.algebra():
            return self._generic_coerce_map(X)
        return self._coerce_map_via([self.algebra(), self.module()], X)

    def _an_element_(self):
        """
        Return an element of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
            sage: A.an_element()
            a
        """
        return self(self.algebra().an_element())

    def some_elements(self):
        """
        Return some elements of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^2 - 1)
            sage: list(A.some_elements())
            [1, ...]
        """
        return (self(x) for x in self.module().some_elements())

    def random_element(self):
        """
        Return a random element of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^2 - 1)
            sage: A.random_element()  # random
            -1/137*a - 1
            sage: B = FiniteFlatAlgebra(QQ, [x, x^2 - 1])
            sage: B.random_element()  # random
            (0, 1/2*a1 - 1/5)
        """
        return self(self.module().random_element())

    @cached_method
    def multiplication_tensor(self):
        """
        Return the multiplication tensor of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^3 - x - 1)
            sage: A.multiplication_tensor()
            [
            [1 0 0]  [0 1 0]  [0 0 1]
            [0 1 0]  [0 0 1]  [1 1 0]
            [0 0 1], [1 1 0], [0 1 1]
            ]
            sage: B = FiniteFlatAlgebra(QQ, [x, x, x^2 - 5])
            sage: B.multiplication_tensor()
            [
            [1 0 0 0]  [0 0 0 0]  [0 0 0 0]  [0 0 0 0]
            [0 0 0 0]  [0 1 0 0]  [0 0 0 0]  [0 0 0 0]
            [0 0 0 0]  [0 0 0 0]  [0 0 1 0]  [0 0 0 1]
            [0 0 0 0], [0 0 0 0], [0 0 0 1], [0 0 5 0]
            ]
        """
        return [x.matrix() for x in self.gens()]

    def finite_dimensional_algebra(self):
        """
        Return a :class:`FiniteDimensionalAlgebra` isomorphic to ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^3 - x - 1)
            sage: A.finite_dimensional_algebra()
            Finite-dimensional algebra of degree 3 over Rational Field
            sage: B = FiniteFlatAlgebra(QQ, [x, x, x^2 - 5])
            sage: B.finite_dimensional_algebra()
            Finite-dimensional algebra of degree 4 over Rational Field
        """
        return FiniteDimensionalAlgebra(self.base_ring(),
                                        self.multiplication_tensor(),
                                        assume_associative=True)

    def to_generic(self):
        """
        Return ``self`` as a generic finite flat algebra.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x^2 + x + 1])
            sage: A.to_generic()
            Finite flat algebra of degree 3 over Rational Field
        """
        return FiniteFlatAlgebra(self.base_ring(),
                                 self.multiplication_tensor())

    @cached_method
    def splitting_field_polynomial(self):
        """
        Return a defining polynomial for the splitting field of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^3 - x - 1)
            sage: A.splitting_field_polynomial()
            x^6 - 6*x^4 + 9*x^2 + 23
            sage: A = FiniteFlatAlgebra(QQ, [x, x^3 - x - 1])
            sage: A.splitting_field_polynomial()
            x^6 - 6*x^4 + 9*x^2 + 23
        """
        from sage.libs.pari import pari
        R = self._polynomial_ring()
        S = set()
        for f in self._irreducible_polys():
            if f.degree() > 1:
                S.add(pari(f).nfsplitting())
        f = pari(R.gen())
        for g in S:
            comp = f.polcompositum(g)
            f = comp[len(comp) - 1]
        return R(f)

    def ramified_primes(self):
        """
        Return the set of ramified primes of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: A.ramified_primes()
            {2}
        """
        from sage.rings.integer_ring import ZZ
        return set(ZZ(self.discriminant()).prime_divisors())


class FiniteFlatAlgebra_monogenic(FiniteFlatAlgebra_base):
    """
    A finite flat algebra over a ring `R`, represented as a quotient
    of the polynomial algebra `R[x]`.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: S.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
        sage: A
        Monogenic algebra of degree 4 over Rational Field with defining polynomial x^4 - 16
        sage: A.category()
        Category of finite dimensional commutative algebras with basis over Rational Field
    """
    Element = FiniteFlatAlgebraElement_monogenic

    def __init__(self, base_ring, poly, basis):
        """
        Initialise a monogenic algebra over ``base_ring``.

        INPUT:

        - ``base_ring`` -- a commutative ring

        - ``poly`` -- a polynomial over ``base_ring``

        - ``basis`` -- a basis for the extension of ``base_ring``
          defined by ``poly``

        This is not meant to be called directly; use
        :class:`FiniteFlatAlgebraFactory` instead.

        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
            sage: TestSuite(A).run()
        """
        self._poly = poly
        self._basis = basis
        super(FiniteFlatAlgebra_monogenic, self).__init__(base_ring)

    def _repr_(self):
        """
        Return a string representation of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
            sage: A
            Monogenic algebra of degree 4 over Rational Field with defining polynomial x^4 - 16
        """
        return ('Monogenic algebra of degree %s over %s with defining polynomial %s'
                % (self.degree(), self.base_ring(), self._poly))

    def degree(self):
        """
        Return the degree of ``self``.
        """
        return self._poly.degree()

    @cached_method
    def _basis_matrix(self):
        """
        Return the matrix of the distinguished basis of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16, [1, 2*x, 4*x^2, 8*x^3])
            sage: A._basis_matrix()
            [1 0 0 0]
            [0 2 0 0]
            [0 0 4 0]
            [0 0 0 8]
        """
        return Matrix(self.base_ring(), [self.algebra()(x).list() for x in self._basis])

    @cached_method
    def algebra(self):
        """
        Return the underlying algebra of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]

            sage: A = FiniteFlatAlgebra(QQ, x^2 + 1)
            sage: alg = A.algebra()
            sage: alg
            Number Field in a with defining polynomial x^2 + 1
            sage: alg.category()
            Category of number fields

            sage: B = FiniteFlatAlgebra(QQ, x^3 + x)
            sage: alg = B.algebra()
            sage: alg
            Univariate Quotient Polynomial Ring in a over Rational Field with modulus x^3 + x
        """
        try:
            return self.base_ring().extension(self._poly, names='a')
        except (ValueError, NotImplementedError):
            return self._poly.parent().quotient(self._poly, names='a')

    def is_field(self):
        """
        Return whether ``self`` is a field.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: FiniteFlatAlgebra(QQ, x^2 + 2).is_field()
            True
            sage: FiniteFlatAlgebra(QQ, x^4 - 16).is_field()
            False
        """
        return self.algebra().is_field()

    def change_ring(self, R):
        """
        Return the base change of ``self`` to `R`.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
            sage: A.change_ring(GF(3))
            Monogenic algebra of degree 4 over Finite Field of size 3 with defining polynomial x^4 + 2
            sage: B = FiniteFlatAlgebra(QQ, x^2 - 1/25, [1, 5*x])
            sage: B.change_ring(GF(5))
            Finite flat algebra of degree 2 over Finite Field of size 5
        """
        if R is self.base_ring():
            return self
        try:
            return FiniteFlatAlgebra(R, self._poly, self._basis)
        except ZeroDivisionError:
            return self.to_generic().change_ring(R)

    def morphisms_to_ring(self, R, as_matrix=False):
        """
        Return all ring homomorphisms from ``self`` to `R`.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^3 - x - 1)
            sage: A.morphisms_to_ring(Qp(23))
            [(1 + O(23^20), 3 + 15*23 + 17*23^2 + 21*23^4 + 21*23^5 + 20*23^6 + 2*23^8 + 6*23^9 + 9*23^10 + 13*23^11 + 19*23^12 + 5*23^13 + 21*23^14 + 5*23^15 + 17*23^16 + 7*23^17 + 20*23^18 + 15*23^19 + O(23^20), 9 + 21*23 + 8*23^2 + 18*23^3 + 16*23^5 + 2*23^6 + 22*23^7 + 19*23^8 + 17*23^9 + 17*23^10 + 13*23^11 + 11*23^13 + 15*23^14 + 20*23^15 + 3*23^16 + 2*23^17 + 15*23^18 + O(23^20))]
            sage: B = FiniteFlatAlgebra(QQ, x^3 - 7)
            sage: B.morphisms_to_ring(QQ)
            []
        """
        d = self.degree()
        roots = self._poly.base_extend(R).roots(multiplicities=False)
        M = Matrix(R, [a.powers(d) for a in roots], ncols=d) \
            * self._basis_matrix().transpose()
        return M if as_matrix else M.rows()

    def _polynomial_ring(self):
        """
        Return the parent of the defining polynomial of ``self``.
        """
        return self._poly.parent()

    def _irreducible_polys(self):
        """
        Return the set of defining polynomials of the irreducible factors
        of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^3 - x - 1)
            sage: A._irreducible_polys()
            {x^3 - x - 1}
        """
        return {f for f, _ in self._poly.factor()}

    @cached_method
    def splitting_field(self, names):
        """
        Return a splitting field for ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^3 - x - 1)
            sage: A.splitting_field('a')
            Number Field in a with defining polynomial x^6 + 3*x^5 + 19*x^4 + 31*x^3 + 121*x^2 + 143*x + 307
        """
        return self._poly.splitting_field(names)

    def discriminant(self):
        """
        Return the discriminant of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16, [1, 1/2*x, 1/4*x^2, 1/8*x^3])
            sage: A.discriminant()
            -256
            sage: B = FiniteFlatAlgebra(QQ, x^2 - 1/25, [1, 5*x])
            sage: B.discriminant()
            4
        """
        return (self._poly.discriminant()
                * self._basis_matrix().determinant() ** 2)


class FiniteFlatAlgebra_product(FiniteFlatAlgebra_base):
    """
    A finite flat algebra over a field `R`, represented as a product
    of finite flat extensions of `R`.
    """
    Element = FiniteFlatAlgebraElement_product

    def __init__(self, base_ring, polys, bases):
        """
        Initialise a finite flat algebra represented as a product.

        INPUT:

        - ``base_ring`` -- a commutative ring

        - ``polys`` -- a tuple of polynomials over ``base_ring``

        - ``basis`` -- a tuple of bases for the respective extensions
          of ``base_ring`` defined by ``polys``

        This is not meant to be called directly; use
        :class:`FiniteFlatAlgebraFactory` instead.

        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x^2 - 2])
            sage: TestSuite(A).run()
        """
        self._polys = polys
        self._degrees = tuple(f.degree() for f in polys)
        try:
            self._factors = tuple(base_ring.extension(f, 'a' + str(i))
                                  for i, f in enumerate(polys))
        except (ValueError, NotImplementedError):
            R = polys[0].parent()
            self._factors = tuple(R.quotient(f, 'a' + str(i))
                                  for i, f in enumerate(polys))
        self._bases = bases
        super(FiniteFlatAlgebra_product, self).__init__(base_ring)

    def _repr_(self):
        """
        Return a string representation of ``self``.
        """
        return ('Finite flat algebra of degree %s over %s, product of:\n'
                % (self.degree(), self.base_ring())
                + '\n'.join(repr(K) for K in self._factors))

    @cached_method
    def degree(self):
        """
        Return the degree of ``self``.
        """
        return sum(self._degrees)

    @cached_method
    def _basis_matrices(self):
        """
        Return the matrices of the distinguished bases of the factors of
        ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x^2 - 1])
            sage: A._basis_matrices()
            [
                 [1 0]
            [1], [0 1]
            ]
        """
        R = self.base_ring()
        def V(F, B):
            try:
                return [F(b)._vector_() for b in B]
            except AttributeError:
                return [F(b).list() for b in B]
        return [Matrix(R, V(F, B)) for F, B in zip(self._factors, self._bases)]

    def _basis_matrix(self):
        """
        Return the matrix of the distinguished basis of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x^2 - 4], [[1], [1, 2*x]])
            sage: A._basis_matrix()
            [1 0 0]
            [0 1 0]
            [0 0 2]
        """
        return Matrix.block_diagonal(self._basis_matrices(), subdivide=False)

    @cached_method
    def algebra(self):
        """
        Return the underlying algebra of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x^2 + 1])
            sage: alg = A.algebra()
            sage: alg
            The Cartesian product of (Number Field in a0 with defining polynomial x, Number Field in a1 with defining polynomial x^2 + 1)
        """
        from sage.categories.all import cartesian_product, CommutativeAlgebras
        category = CommutativeAlgebras(self.base_ring()).CartesianProducts()
        return cartesian_product(self._factors, category=category)

    def is_field(self):
        """
        Return whether ``self`` is a field.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: FiniteFlatAlgebra(QQ, [R(1), x]).is_field()
            True
            sage: FiniteFlatAlgebra(QQ, [x, x^2 + 1]).is_field()
            False
        """
        F = [R for R in self._factors if not R.is_zero()]
        return len(F) == 1 and F[0].is_field()

    def change_ring(self, R):
        """
        Return the base change of ``self`` to `R`.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x^2 + x + 1])
            sage: A.change_ring(GF(3))
            Finite flat algebra of degree 3 over Finite Field of size 3, product of:
            Finite Field of size 3
            Univariate Quotient Polynomial Ring in a1 over Finite Field of size 3 with modulus a1^2 + a1 + 1
            sage: B = FiniteFlatAlgebra(QQ, [x, x^2 - 1/25], [[1], [1, 5*x]])
            sage: B.change_ring(GF(5))
            Finite flat algebra of degree 3 over Finite Field of size 5
        """
        if R is self.base_ring():
            return self
        try:
            return FiniteFlatAlgebra(R, self._polys, self._bases)
        except ZeroDivisionError:
            return self.to_generic().change_ring(R)

    def morphisms_to_ring(self, R, as_matrix=False):
        """
        Return all ring homomorphisms from ``self`` to `R`.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x^2 - 1])
            sage: A.morphisms_to_ring(QQ)
            [(1, 0, 0), (0, 1, 1), (0, 1, -1)]
        """
        M = []
        for F, basis in zip(self._factors, self._basis_matrices()):
            try:
                f = F.modulus()
            except AttributeError:
                f = F.defining_polynomial()
            d = f.degree()
            roots = f.base_extend(R).roots(multiplicities=False)
            if len(roots) == 0:
                B = Matrix(R, 0, d)
            else:
                B = Matrix(R, [a.powers(d) for a in roots]) * basis.transpose()
            M.append(B)
        M = Matrix.block_diagonal(M, subdivide=False)
        return M if as_matrix else M.rows()

    def _polynomial_ring(self):
        """
        Return the parent of the defining polynomials of ``self``.
        """
        # TODO: trivial case of the zero algebra
        return self._polys[0].parent()

    def _irreducible_polys(self):
        """
        Return the set of defining polynomials of the irreducible factors
        of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: FiniteFlatAlgebra(QQ, [x, x])._irreducible_polys()
            {x}
            sage: FiniteFlatAlgebra(QQ, [x, x^3 + x])._irreducible_polys()
            {x, x^2 + 1}
        """
        S = set()
        for f in self._polys:
            S.update(g for g, _ in f.factor())
        return S

    @cached_method
    def splitting_field(self, names):
        """
        Return a splitting field for ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: FiniteFlatAlgebra(QQ, [x, x^3 + x]).splitting_field('a')
            Number Field in a with defining polynomial x^2 + 1
        """
        from sage.misc.all import prod
        poly = prod(self._polys)
        return poly.splitting_field(names)

    def discriminant(self):
        """
        Return the discriminant of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x^2 - 4], [[1], [1, 1/2*x]])
            sage: A.discriminant()
            4
        """
        from sage.misc.all import prod
        return prod(f.discriminant() * M.determinant() ** 2
                    for f, M in zip(self._polys, self._basis_matrices()))

    if not hasattr(sage.categories.unital_algebras.UnitalAlgebras.ParentMethods,
                   '_coerce_map_from_base_ring'):

        # Compatibility with Sage versions before 9.1.beta6

        _no_generic_basering_coercion = True

        @cached_method
        def algebra(self):
            from sage.categories.all import cartesian_product, CommutativeRings
            category = CommutativeRings().CartesianProducts()
            return cartesian_product(self._factors, category=category)

        def _coerce_map_from_(self, X):
            R = self.base_ring()
            if X is R:
                from sage.categories.poor_man_map import PoorManMap
                return PoorManMap(lambda x: self.element_class(self, [K(x) for K in self._factors]),
                                  domain=R, codomain=self)
            f = self._coerce_map_via([R], X)
            if f is not None:
                return f
            return super(FiniteFlatAlgebra_product, self)._coerce_map_from_(X)


class FiniteFlatAlgebra_generic(FiniteFlatAlgebra_base):
    """
    A finite flat algebra over a ring `R`, represented as a generic
    finite algebra (see :class:`FiniteDimensionalAlgebra`).

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
        sage: A
        Finite flat algebra of degree 2 over Rational Field
        sage: A.category()
        Category of finite dimensional commutative algebras with basis over Rational Field
    """
    Element = FiniteFlatAlgebraElement_generic

    def __init__(self, base_ring, matrices):
        """
        Initialise a monogenic algebra over ``base_ring``.

        INPUT:

        - ``base_ring`` -- a commutative ring

        - ``matrices`` -- a list of matrices

        This is not meant to be called directly; use
        :class:`FiniteFlatAlgebraFactory` instead.

        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: TestSuite(A).run(skip=['_test_elements', '_test_pickling'])
        """
        self._algebra = FiniteDimensionalAlgebra(base_ring, matrices,
                                                 assume_associative=True)
        super(FiniteFlatAlgebra_generic, self).__init__(base_ring)

    def _repr_(self):
        """
        Return a string representation of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: A
            Finite flat algebra of degree 2 over Rational Field
        """
        return ('Finite flat algebra of degree %s over %s'
                % (self.degree(), self.base_ring()))

    def degree(self):
        """
        Return the degree of ``self``.
        """
        return self._algebra.degree()

    @cached_method
    def _basis_matrix(self):
        """
        Return the matrix of the distinguished basis of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: A._basis_matrix()
            [1 0]
            [0 1]
        """
        return Matrix.identity(self.degree())

    def algebra(self):
        """
        Return the underlying algebra of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: alg = A.algebra()
            sage: alg
            Finite-dimensional algebra of degree 2 over Rational Field
            sage: alg.category()
            Category of finite dimensional associative algebras with basis over Rational Field
        """
        return self._algebra

    def change_ring(self, R):
        """
        Return the base change of ``self`` to `R`.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: A.change_ring(GF(2))
            Finite flat algebra of degree 2 over Finite Field of size 2
        """
        if R is self.base_ring():
            return self
        A = self._algebra
        return FiniteFlatAlgebra(R, [M.change_ring(R) for M in A.table()])

    def morphisms_to_ring(self, R, as_matrix=False):
        """
        Return all ring homomorphisms from ``self`` to `R`.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: A.morphisms_to_ring(GF(2))
            [(1, 1)]
            sage: A.morphisms_to_ring(GF(3))
            []
            sage: A.morphisms_to_ring(GF(5))
            [(1, 3), (1, 2)]
            sage: A.morphisms_to_ring(Qp(23))
            Traceback (most recent call last):
            ...
            PrecisionError: p-adic factorization not well-defined since the discriminant is zero up to the requestion p-adic precision
        """
        A = self.change_ring(R).algebra()
        n = self.degree()
        H = []
        for m in A.maximal_ideals():
            B = m.basis_matrix()
            if m.basis_matrix().nrows() == n - 1:
                C = Matrix([A.one().vector()] + B.rows())
                h = C.solve_right(C.row_space().gen(0))
                H.append(h)
        return Matrix(H) if as_matrix else H

    def _irreducible_polys(self):
        """
        Return the set of irreducible factors of the characteristic
        polynomials of the distinguished basis elements of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: A._irreducible_polys()
            {x - 1, x^2 + 1}
        """
        S = set()
        for x in self.gens():
            S.update(g for g, _ in x.matrix().characteristic_polynomial().factor())
        return S

    @cached_method
    def splitting_field(self, names):
        """
        Return a splitting field for ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: A.splitting_field('a')
            Number Field in a with defining polynomial x^2 + 1
        """
        from sage.misc.all import prod
        poly = prod(self._irreducible_polys())
        return poly.splitting_field(names)

    def discriminant(self):
        """
        Return the discriminant of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: A.discriminant()
            -4
        """
        return Matrix([[(a * b).matrix().trace() for a in self.gens()]
                       for b in self.gens()]).determinant()

class FiniteFlatAlgebraFactory(UniqueFactory):
    """
    Factory for finite flat algebras.
    """

    def create_key(self, base_ring, *data):
        """
        Return a key for the algebra defined by the given data.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: FiniteFlatAlgebra.create_key(QQ, x^2 + 1)
            (Rational Field, x^2 + 1, (1, x))
            sage: FiniteFlatAlgebra.create_key(QQ, [x, x^2 + 1])
            (Rational Field, (x, x^2 + 1), ((1,), (1, x)))
            sage: FiniteFlatAlgebra.create_key(QQ, x^3 - x - 1, [1, x^2 - 1, x])
            (Rational Field, x^3 - x - 1, (1, x^2 - 1, x))
            sage: FiniteFlatAlgebra.create_key(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            (Rational Field, (
            [1 0]  [ 0  1]
            [0 1], [-1  0]
            ))
        """
        def _make_basis(R, B):
            if isinstance(B, sage.matrix.matrix0.Matrix):
                B = map(tuple, (~B).columns())
            return tuple(map(R, B))

        if isinstance(data[0], (list, tuple)):
            if len(data[0]) > 0 and isinstance(data[0][0], sage.matrix.matrix0.Matrix):
                matrices = tuple(M.change_ring(base_ring) for M in data[0])
                return (base_ring, matrices)
            polys = tuple(f.change_ring(base_ring) for f in data[0])
            if len(data) == 1 or data[1] is None:
                bases = [None] * len(polys)
            else:
                bases = list(data[1])
            for i, f in enumerate(polys):
                if bases[i] is None:
                    bases[i] = f.parent().gen().powers(f.degree())
                bases[i] = _make_basis(f.parent(), bases[i])
            return (base_ring, polys, tuple(bases))
        else:
            poly = data[0].change_ring(base_ring)
            if len(data) == 1 or data[1] is None:
                basis = poly.parent().gen().powers(poly.degree())
            else:
                basis = data[1]
            basis = _make_basis(poly.parent(), basis)
            return (base_ring, poly, basis)

    def create_object(self, version, key):
        """
        Return the algebra defined by the given key.

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: FiniteFlatAlgebra.create_object((8, 8), (QQ, x^2 + 1, (R(1), x)))
            Monogenic algebra of degree 2 over Rational Field with defining polynomial x^2 + 1
            sage: FiniteFlatAlgebra.create_object((8, 8), (QQ, (x, x^2 + 1), ((R(1),), (R(1), x))))
            Finite flat algebra of degree 3 over Rational Field, product of:
            Number Field in a0 with defining polynomial x
            Number Field in a1 with defining polynomial x^2 + 1
            sage: FiniteFlatAlgebra.create_object((8, 8), (QQ, x^3 - x - 1, (R(1), x^2 - 1, x)))
            Monogenic algebra of degree 3 over Rational Field with defining polynomial x^3 - x - 1
            sage: FiniteFlatAlgebra.create_object((8, 8), (QQ, (Matrix(QQ, [[1,0], [0,1]]), Matrix(QQ, [[0,1], [-1,0]]))))
            Finite flat algebra of degree 2 over Rational Field
        """
        if isinstance(key[1], tuple):
            if len(key[1]) > 0 and isinstance(key[1][0], sage.matrix.matrix0.Matrix):
                return FiniteFlatAlgebra_generic(*key)
            else:
                return FiniteFlatAlgebra_product(*key)
        else:
            return FiniteFlatAlgebra_monogenic(*key)


FiniteFlatAlgebra = FiniteFlatAlgebraFactory("dual_pairs.finite_flat_algebra.FiniteFlatAlgebra")
