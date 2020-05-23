# -*- coding: utf-8 -*-
"""
Finite locally free modules over finite flat algebras.
"""

from __future__ import absolute_import

from sage.modules.module import Module
from sage.structure.element import ModuleElement

from .finite_flat_algebra import FiniteFlatAlgebra_base


class FiniteFlatAlgebraModuleElement(ModuleElement):
    """
    An element of a free module of rank 1 over a finite flat algebra.

    Currently, these are just represented as algebra elements.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
        sage: M = FiniteFlatAlgebraModule(A)
        sage: m = M(1)
        sage: m
        1
        sage: m + m
        2
        sage: 2*m - A(x)*m
        -a + 2
        sage: -m
        -1
        sage: A(x) * m
        a
    """
    def __init__(self, parent, x):
        """
        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
            sage: M = FiniteFlatAlgebraModule(A)
            sage: m = M(1)
            sage: TestSuite(m).run(skip=['_test_pickling'])
        """
        self._set_parent(parent)
        self._algebra_element = parent.base_ring()(x)

    def _repr_(self):
        """
        TODO
        """
        return repr(self._algebra_element)

    def _richcmp_(self, other, op):
        """
        TODO
        """
        return self._algebra_element._richcmp_(other._algebra_element, op)

    def _add_(self, other):
        """
        TODO
        """
        P = self.parent()
        z = self._algebra_element + other._algebra_element
        return P.element_class(P, z)

    def _sub_(self, other):
        """
        TODO
        """
        P = self.parent()
        z = self._algebra_element - other._algebra_element
        return P.element_class(P, z)

    def _neg_(self):
        """
        TODO
        """
        P = self.parent()
        z = -self._algebra_element
        return P.element_class(P, z)

    def _lmul_(self, other):
        """
        TODO
        """
        P = self.parent()
        z = self._algebra_element * other
        return P.element_class(P, z)

    _rmul_ = _lmul_

    def module_element(self):
        """
        Return ``self`` as a module element over the *base ring* of the
        finite flat algebra that is the base ring of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
            sage: M = FiniteFlatAlgebraModule(A)
            sage: M(x).module_element()
            (0, 1, 0, 0)
        """
        return self._algebra_element.module_element()


class FiniteFlatAlgebraModule(Module):
    """
    A locally free module of rank 1 over a finite flat algebra.

    Currently, only free modules are supported.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra
        sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
        sage: M = FiniteFlatAlgebraModule(A)
        sage: M.zero()
        0
        sage: M.coerce_map_from(QQ)
        sage: M.coerce_map_from(A)
    """
    Element = FiniteFlatAlgebraModuleElement

    def __init__(self, R):
        """
        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^4 - 16)
            sage: M = FiniteFlatAlgebraModule(A)
            sage: TestSuite(M).run(skip=['_test_elements', '_test_pickling'])
        """
        if not isinstance(R, FiniteFlatAlgebra_base):
            raise TypeError("base ring must be a finite flat algebra")
        super(FiniteFlatAlgebraModule, self).__init__(R)

    def _repr_(self):
        """
        Return a string representation of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^2 + 1)
            sage: M = FiniteFlatAlgebraModule(A)
            sage: M
            Free module of rank 1 over Monogenic algebra of degree 2 over Rational Field with defining polynomial x^2 + 1
        """
        return "Free module of rank 1 over %s" % self.base_ring()

    def change_ring(self, R):
        """
        Return a copy of ``self`` base-changed to `R`.

        .. TODO::

            If `A` is the finite flat algebra over which ``self`` is a
            module, should `R` be an algebra over `A` or over the base
            ring of `A`?

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^2 + 1)
            sage: M = FiniteFlatAlgebraModule(A)
            sage: M.change_ring(QuadraticField(-1, 'i'))
            Traceback (most recent call last):
            ...
            TypeError: base ring must be a finite flat algebra
        """
        if self.base_ring() is R:
            return self
        return FiniteFlatAlgebraModule(R)

    def random_element(self):
        """
        Return a random element of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^2 - 1)
            sage: M = FiniteFlatAlgebraModule(A)
            sage: M.random_element()  # random
            -1/95*a - 1/2
        """
        return self(self.base_ring().random_element())

    def dual(self):
        """
        Return the dual of ``self`` over its base ring.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, x^2 + 1)
            sage: M = FiniteFlatAlgebraModule(A)
            sage: M.dual()
            Free module of rank 1 over Monogenic algebra of degree 2 over Rational Field with defining polynomial x^2 + 1
        """
        return FiniteFlatAlgebraModule(self.base_ring())
