# -*- coding: utf-8 -*-
"""
Elements of finite flat algebras.
"""

from __future__ import absolute_import

from sage.matrix.all import Matrix
from sage.rings.finite_rings.element_base import FiniteRingElement
from sage.structure.element import AlgebraElement, RingElement, ModuleElement


def _list_to_alg(A, v):
    """
    Return the element of `A` defined by the list `v`.
    """
    if len(v) == 1:
        return A(v[0])
    return A(v)

def _alg_to_list(x):
    """
    Return the list of coefficients of the algebra element `x`.
    """
    if isinstance(x, FiniteRingElement):
        return x._vector_().list()
    return x.list()


class FiniteFlatAlgebraElement(AlgebraElement):
    """
    An element of a finite flat algebra.

    This is an abstract base class.
    """

    def _repr_(self):
        """
        TODO
        """
        return repr(self.algebra_element())

    def _richcmp_(self, other, op):
        """
        TODO
        """
        return self.module_element()._richcmp_(other.module_element(), op)

    def _add_(self, other):
        """
        TODO
        """
        P = self.parent()
        z = self.module_element() + other.module_element()
        return P.element_class(P, z)

    def _sub_(self, other):
        """
        TODO
        """
        P = self.parent()
        z = self.module_element() - other.module_element()
        return P.element_class(P, z)

    def _neg_(self):
        """
        TODO
        """
        P = self.parent()
        z = -self.module_element()
        return P.element_class(P, z)

    def _mul_(self, other):
        """
        TODO
        """
        P = self.parent()
        z = self.algebra_element() * other.algebra_element()
        return P.element_class(P, z)

    def _lmul_(self, x):
        """
        Return the product of ``self`` with `x`.

        INPUT:

            - `x` -- an element of the base ring of ``self``

        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x^2 - 2])
            sage: A.gen(2) * QQ.one()
            (0, a1)
        """
        P = self.parent()
        z = self.module_element() * x
        return P.element_class(P, z)

    def __invert__(self):
        """
        Return the inverse of ``self``.

        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^2 - 2)
            sage: ~A(x)
            1/2*a
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: ~A.gen(1)
            -e1
            sage: A = FiniteFlatAlgebra(QQ, [x])
            sage: ~A.gen(0)
            (1,)
        """
        P = self.parent()
        z = ~self.algebra_element()
        return P.element_class(P, z)

    def is_unit(self):
        """
        TODO
        """
        return self.algebra_element().is_unit()

    def inverse_of_unit(self):
        """
        TODO
        """
        P = self.parent()
        z = self.algebra_element().inverse_of_unit()
        return P.element_class(P, z)

    def monomial_coefficients(self, **kwds):
        """
        Return a dictionary containing the coefficients of ``self``.

        This method is required by :class:`ModulesWithBasis`.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^2 - 1)
            sage: a = A(x)
            sage: (3*a + 2).monomial_coefficients()
            {0: 2, 1: 3}
        """
        return dict(enumerate(self.module_element(**kwds)))

    def _im_gens_(self, codomain, im_gens, base_map):
        """
        TODO
        """
        m = self.module_element()
        if base_map is not None:
            m = m.apply_map(base_map)
        return codomain(sum(a * x for a, x in zip(m, im_gens)))


class FiniteFlatAlgebraElement_monogenic(FiniteFlatAlgebraElement):
    """
    An element of a monogenic finite flat algebra.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: S.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
        sage: a = A(x)
        sage: type(a)
        <class 'dual_pairs.finite_flat_algebra.FiniteFlatAlgebra_monogenic_with_category.element_class'>
        sage: a
        a
    """
    def __init__(self, parent, x):
        """
        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: S.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
            sage: a = A(x)
            sage: TestSuite(a).run()
        """
        self._set_parent(parent)
        if isinstance(x, RingElement):
            self._algebra_element = parent.algebra()(x)
        else:
            self._module_element = parent.module()(x)

    def algebra_element(self):
        """
        Return the element of the underlying algebra corresponding to
        ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^3 - x - 1)
            sage: A(x).algebra_element()
            a

            sage: R.<x> = GF(3)[]
            sage: A = FiniteFlatAlgebra(GF(3), x^2 - 2)
            sage: A(x).algebra_element()
            a
        """
        try:
            return self._algebra_element
        except AttributeError:
            A = self.parent()
            x = _list_to_alg(A.algebra(), (self._module_element * A._basis_matrix()).list())
            self._algebra_element = x
            return x

    def module_element(self):
        """
        Return the element of the underlying module corresponding to
        ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^3 - x - 1)
            sage: A(x).module_element()
            (0, 1, 0)

            sage: F.<c> = GF(9)
            sage: R.<x> = F[]
            sage: A = FiniteFlatAlgebra(F, x^3 - 1)
            sage: A(x^2).module_element()
            (0, 0, 1)
        """
        try:
            v = self._module_element
        except AttributeError:
            A = self.parent()
            v = A.module()(_alg_to_list(self._algebra_element)) * A._basis_matrix_inv()
            self._module_element = v
        return v

    def matrix(self):
        """
        Return the matrix of multiplication by ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^3 - x - 1)
            sage: A(x).matrix()
            [0 1 0]
            [0 0 1]
            [1 1 0]
        """
        A = self.parent()
        B = A._basis_matrix()
        Binv = A._basis_matrix_inv()
        return B * self.algebra_element().matrix() * Binv


class FiniteFlatAlgebraElement_product(FiniteFlatAlgebraElement):
    """
    An element of a finite flat algebra presented as a product.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: S.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
        sage: a = A([1, 2, x])
        sage: type(a)
        <class 'dual_pairs.finite_flat_algebra.FiniteFlatAlgebra_product_with_category.element_class'>
        sage: a
        (1, 2, a2)
    """
    def __init__(self, parent, x):
        """
        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: S.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: a = A([1, 2, x])
            sage: TestSuite(a).run()
        """
        self._set_parent(parent)
        if isinstance(x, ModuleElement):
            self._module_element = parent.module()(x)
        else:
            self._algebra_element = parent.algebra()(x)

    def algebra_element(self):
        """
        Return the element of the underlying algebra corresponding to
        ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 - 5])
            sage: A([1, 2, x]).algebra_element()
            (1, 2, a2)

            sage: F.<c> = GF(9)
            sage: R.<x> = F[]
            sage: A = FiniteFlatAlgebra(F, [x, x, x])
            sage: A([x, 1, 2]).module_element()
            (0, 1, 2)
        """
        try:
            return self._algebra_element
        except AttributeError:
            A = self.parent()
            v = (self._module_element * A._basis_matrix()).list()
            x = []
            for i, F in enumerate(A._factors):
                d = A._degrees[i]
                x.append(_list_to_alg(F, v[0:d]))
                v = v[d:]
            self._algebra_element = A.algebra()(x)
            return self._algebra_element

    def module_element(self):
        """
        Return the element of the underlying module corresponding to
        ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 - 5])
            sage: A([1, 2, x]).module_element()
            (1, 2, 0, 1)

            sage: R.<x> = GF(3)[]
            sage: A = FiniteFlatAlgebra(GF(3), [x, x^2 - 2])
            sage: A([2, x]).algebra_element()
            (2, a1)
        """
        try:
            v = self._module_element
        except AttributeError:
            A = self.parent()
            v = (A.module()(sum((_alg_to_list(x) for x in self._algebra_element), []))
                 * A._basis_matrix_inv())
            self._module_element = v
        return v

    def matrix(self):
        """
        Return the matrix of multiplication by ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 - 5])
            sage: A([1, 2, x]).matrix()
            [1 0 0 0]
            [0 2 0 0]
            [0 0 0 1]
            [0 0 5 0]
        """
        A = self.parent()
        B = A._basis_matrix()
        Binv = A._basis_matrix_inv()
        D = Matrix.block_diagonal([u.matrix() for u in self.algebra_element()],
                                  subdivide=False)
        return B * D * Binv


class FiniteFlatAlgebraElement_generic(FiniteFlatAlgebraElement):
    """
    An element of a generic finite flat algebra.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
        sage: a = A.gen(1)
        sage: type(a)
        <class 'dual_pairs.finite_flat_algebra.FiniteFlatAlgebra_generic_with_category.element_class'>
        sage: a
        e1
    """
    def __init__(self, parent, x):
        """
        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: a = A.gen(1)
            sage: TestSuite(a).run(skip=['_test_pickling'])
        """
        self._set_parent(parent)
        if isinstance(x, AlgebraElement):
            self._algebra_element = parent.algebra()(x)
        else:
            self._module_element = parent.module()(x)

    def algebra_element(self):
        """
        Return the element of the underlying algebra corresponding to
        ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: A.gen(1).algebra_element()
            e1
        """
        try:
            return self._algebra_element
        except AttributeError:
            x = self.parent().algebra()(self._module_element)
            self._algebra_element = x
            return x

    def module_element(self):
        """
        Return the element of the underlying module corresponding to
        ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: A.gen(1).module_element()
            (0, 1)
        """
        try:
            v = self._module_element
        except AttributeError:
            v = self._algebra_element.vector()
            self._module_element = v
        return v

    def matrix(self):
        """
        Return the matrix of multiplication by ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: A = FiniteFlatAlgebra(QQ, [Matrix([[1,0], [0,1]]), Matrix([[0,1], [-1,0]])])
            sage: A.gen(1).matrix()
            [ 0 1]
            [-1 0]
        """
        return self.algebra_element().matrix()
