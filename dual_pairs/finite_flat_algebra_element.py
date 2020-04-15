# -*- coding: utf-8 -*-
"""
Elements of finite flat algebras.
"""

from __future__ import absolute_import

from sage.matrix.all import Matrix
from sage.structure.element import (AlgebraElement, CommutativeAlgebraElement,
                                    CommutativeRingElement, ModuleElement)


class FiniteFlatAlgebraElement(CommutativeAlgebraElement):
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
        if isinstance(x, CommutativeRingElement):
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
        """
        try:
            return self._algebra_element
        except AttributeError:
            A = self.parent()
            x = A.algebra()((self._module_element * A._basis_matrix()).list())
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
        """
        try:
            v = self._module_element
        except AttributeError:
            A = self.parent()
            v = A.module()(self._algebra_element.list()) * A._basis_matrix_inv()
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
        """
        try:
            return self._algebra_element
        except AttributeError:
            A = self.parent()
            v = (self._module_element * A._basis_matrix()).list()
            x = []
            for i, F in enumerate(A._factors):
                d = A._degrees[i]
                x.append(F(v[0:d]))
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
        """
        try:
            v = self._module_element
        except AttributeError:
            A = self.parent()
            v = (A.module()(sum((x.list() for x in self._algebra_element), []))
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
