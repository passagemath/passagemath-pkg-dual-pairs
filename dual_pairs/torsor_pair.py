# -*- coding: utf-8 -*-
"""
Torsors under commutative finite flat group schemes.
"""

from __future__ import absolute_import

from sage.misc.all import cached_method
from sage.structure.category_object import CategoryObject


class TorsorPair(CategoryObject):
    """
    A torsor for a dual pair of algebras.

    EXAMPLES::

        sage: from dual_pairs import FiniteFlatAlgebra, DualPair
        sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
        sage: from dual_pairs.torsor_pair import TorsorPair
        sage: R.<x> = QQ[]
        sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
        sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
        ....:                   [1/4,  1/4, -1/2,   0],
        ....:                   [1/2, -1/2,    0,   0],
        ....:                   [  0,    0,    0, -17]])
        sage: D = DualPair(A, Phi)
        sage: T = FiniteFlatAlgebra(QQ, x^4 - 17)
        sage: U = FiniteFlatAlgebraModule(A)
        sage: Psi = Matrix(QQ, [[1, 0, 0,   0],
        ....:                   [0, 0, 1,   0],
        ....:                   [0, 1, 0,   0],
        ....:                   [0, 0, 0, -17]])
        sage: X = TorsorPair(D, T, U, Psi)
        sage: X
        Torsor for Dual pair of algebras over Rational Field
        A = Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x
        Number Field in a2 with defining polynomial x^2 + 17
        B = Finite flat algebra of degree 4 over Rational Field, product of:
        Number Field in a0 with defining polynomial x
        Number Field in a1 with defining polynomial x
        Number Field in a2 with defining polynomial x^2 + 17
        T = Monogenic algebra of degree 4 over Rational Field with defining polynomial x^4 - 17

        sage: from dual_pairs import FiniteFlatAlgebra, DualPair
        sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
        sage: from dual_pairs.torsor_pair import TorsorPair

        sage: A = FiniteFlatAlgebra(QQ, [x^3 - 1])
        sage: B = FiniteFlatAlgebra(QQ, [x, x, x])
        sage: Phi = Matrix.identity(QQ, 3)
        sage: D = DualPair(A, B, Phi)

        sage: t = polygen(QQ, 't')
        sage: T = FiniteFlatAlgebra(QQ, t^3 - 7)
        sage: U = FiniteFlatAlgebraModule(A)
        sage: Psi = Matrix.identity(QQ, 3)
        sage: X = TorsorPair(D, T, U, Psi)

        sage: L.<a> = X.splitting_field()
        sage: points_D = D.points(L)
        sage: points_X = X.points(L)
        sage: Matrix([[points_X.index(X.add(P, Q))
        ....:          for Q in points_X] for P in points_D])
        [0 1 2]
        [1 2 0]
        [2 0 1]
    """

    def __init__(self, dual_pair, T, U, psi):
        r"""
        Initialise a torsor pair.

        INPUT:

        - ``dual_pair`` -- a dual pair `(A, B, \Phi)` of finite flat
          algebras over a ring `R`

        - ``T`` -- a finite flat `R`-algebra of the same degree as `A`
          (and `B`)

        - ``U`` -- a locally free `B`-module of rank 1

        - ``psi`` -- a perfect `R`-bilinear pairing `T \times U \to R`

        TESTS::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: from dual_pairs.torsor_pair import TorsorPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: T = FiniteFlatAlgebra(QQ, x^4 - 17)
            sage: U = FiniteFlatAlgebraModule(A)
            sage: Psi = Matrix(QQ, [[1, 0, 0,   0],
            ....:                   [0, 0, 1,   0],
            ....:                   [0, 1, 0,   0],
            ....:                   [0, 0, 0, -17]])
            sage: X = TorsorPair(D, T, U, Psi)
            sage: TestSuite(X).run(skip=['_test_pickling'])
        """
        from sage.matrix.all import MatrixSpace
        R = dual_pair.base_ring()
        n = dual_pair.degree()
        M = MatrixSpace(R, n, n)
        self._dual_pair = dual_pair
        self._torsor_algebra = T
        self._dual_module = U
        self._psi = M(psi)
        super(TorsorPair, self).__init__(base=R)

    def _repr_(self):
        """
        Return a string representation of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: from dual_pairs.torsor_pair import TorsorPair

            sage: x = polygen(QQ, 'x')
            sage: y = polygen(QQ, 'y')
            sage: A = FiniteFlatAlgebra(QQ, [x^3 - 1])
            sage: B = FiniteFlatAlgebra(QQ, [y, y, y])
            sage: Phi = Matrix.identity(QQ, 3)
            sage: D = DualPair(A, B, Phi)

            sage: t = polygen(QQ, 't')
            sage: T = FiniteFlatAlgebra(QQ, t^3 - 7)
            sage: U = FiniteFlatAlgebraModule(A)
            sage: Psi = Matrix.identity(QQ, 3)
            sage: X = TorsorPair(D, T, U, Psi)
            sage: X
            Torsor for Dual pair of algebras over Rational Field
            A = Finite flat algebra of degree 3 over Rational Field, product of:
            Univariate Quotient Polynomial Ring in a0 over Rational Field with modulus x^3 - 1
            B = Finite flat algebra of degree 3 over Rational Field, product of:
            Number Field in a0 with defining polynomial y
            Number Field in a1 with defining polynomial y
            Number Field in a2 with defining polynomial y
            T = Monogenic algebra of degree 3 over Rational Field with defining polynomial t^3 - 7
        """
        return ('Torsor for %s\nT = %s'
                % (self.dual_pair(), self.algebra()))

    def dual_pair(self):
        """
        Return the dual pair for which ``self`` is a torsor.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: from dual_pairs.torsor_pair import TorsorPair

            sage: x = polygen(QQ, 'x')
            sage: y = polygen(QQ, 'y')
            sage: A = FiniteFlatAlgebra(QQ, [x^3 - 1])
            sage: B = FiniteFlatAlgebra(QQ, [y, y, y])
            sage: Phi = Matrix.identity(QQ, 3)
            sage: D = DualPair(A, B, Phi)

            sage: t = polygen(QQ, 't')
            sage: T = FiniteFlatAlgebra(QQ, t^3 - 7)
            sage: U = FiniteFlatAlgebraModule(A)
            sage: Psi = Matrix.identity(QQ, 3)
            sage: X = TorsorPair(D, T, U, Psi)
            sage: X.dual_pair() is D
            True
        """
        return self._dual_pair

    def algebra(self):
        """
        Return the `R`-algebra `T` attached to ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: from dual_pairs.torsor_pair import TorsorPair

            sage: x = polygen(QQ, 'x')
            sage: y = polygen(QQ, 'y')
            sage: A = FiniteFlatAlgebra(QQ, [x^3 - 1])
            sage: B = FiniteFlatAlgebra(QQ, [y, y, y])
            sage: Phi = Matrix.identity(QQ, 3)
            sage: D = DualPair(A, B, Phi)

            sage: t = polygen(QQ, 't')
            sage: T = FiniteFlatAlgebra(QQ, t^3 - 7)
            sage: U = FiniteFlatAlgebraModule(A)
            sage: Psi = Matrix.identity(QQ, 3)
            sage: X = TorsorPair(D, T, U, Psi)
            sage: X.algebra() is T
            True
        """
        return self._torsor_algebra

    def dual_module(self):
        """
        Return the `B`-module `U` attached to ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: from dual_pairs.torsor_pair import TorsorPair

            sage: x = polygen(QQ, 'x')
            sage: y = polygen(QQ, 'y')
            sage: A = FiniteFlatAlgebra(QQ, [x^3 - 1])
            sage: B = FiniteFlatAlgebra(QQ, [y, y, y])
            sage: Phi = Matrix.identity(QQ, 3)
            sage: D = DualPair(A, B, Phi)

            sage: t = polygen(QQ, 't')
            sage: T = FiniteFlatAlgebra(QQ, t^3 - 7)
            sage: U = FiniteFlatAlgebraModule(A)
            sage: Psi = Matrix.identity(QQ, 3)
            sage: X = TorsorPair(D, T, U, Psi)
            sage: X.dual_module() is U
            True
        """
        return self._dual_module

    def psi(self):
        r"""
        Return the pairing matrix :math:`\Psi` attached to ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: from dual_pairs.torsor_pair import TorsorPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: T = FiniteFlatAlgebra(QQ, x^4 - 17)
            sage: U = FiniteFlatAlgebraModule(A)
            sage: Psi = Matrix(QQ, [[1, 0, 0,   0],
            ....:                   [0, 0, 1,   0],
            ....:                   [0, 1, 0,   0],
            ....:                   [0, 0, 0, -17]])
            sage: X = TorsorPair(D, T, U, Psi)
            sage: X.psi() == Psi
            True
        """
        return self._psi

    @cached_method
    def upsilon(self):
        r"""
        Return the matrix :math:`\Upsilon` attached to ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: from dual_pairs.torsor_pair import TorsorPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: T = FiniteFlatAlgebra(QQ, x^4 - 17)
            sage: U = FiniteFlatAlgebraModule(A)
            sage: Psi = Matrix(QQ, [[1, 0, 0,   0],
            ....:                   [0, 0, 1,   0],
            ....:                   [0, 1, 0,   0],
            ....:                   [0, 0, 0, -17]])
            sage: X = TorsorPair(D, T, U, Psi)
            sage: X.upsilon()
            [    1     0     0     0]
            [    0     0     1     0]
            [    0     1     0     0]
            [    0     0     0 -1/17]
        """
        return self.psi().transpose().inverse()

    def is_isomorphic(self, other):
        """
        Return ``True`` if ``self`` is isomorphic to ``other``.

        .. TODO::

            - more efficient algorithm

            - optionally also return an isomorphism

        """
        return self.isom_torsor(other).is_trivial()

    def is_trivial(self):
        """
        Return ``True`` if ``self`` is a trivial torsor.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: from dual_pairs.torsor_pair import TorsorPair

            sage: x = polygen(QQ, 'x')
            sage: y = polygen(QQ, 'y')
            sage: A = FiniteFlatAlgebra(QQ, [x^3 - 1])
            sage: B = FiniteFlatAlgebra(QQ, [y, y, y])
            sage: Phi = Matrix.identity(QQ, 3)
            sage: D = DualPair(A, B, Phi)
            sage: X = D.trivial_torsor()
            sage: X.is_trivial()
            True

            sage: t = polygen(QQ, 't')
            sage: T = FiniteFlatAlgebra(QQ, t^3 - 7)
            sage: U = FiniteFlatAlgebraModule(A)
            sage: Psi = Matrix.identity(QQ, 3)
            sage: X = TorsorPair(D, T, U, Psi)
            sage: X.is_trivial()
            False
        """
        return self.points(self.base_ring()) != []

    def opposite(self):
        """
        Return the opposite torsor of ``self``.

        TODO: is this a good name?
        """
        raise NotImplementedError

    def contracted_product(self):
        """
        Return the contracted product of ``self`` and ``other``.

        TODO: is this a good name?
        """
        raise NotImplementedError

    def isom_torsor(self, other):
        """
        Return the torsor ``Isom(self, other)``.

        TODO: is this a good name?
        """
        raise NotImplementedError

    def points(self, R):
        """
        Return the set of points of ``self`` over `R`.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: from dual_pairs.torsor_pair import TorsorPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: T = FiniteFlatAlgebra(QQ, x^4 - 17)
            sage: U = FiniteFlatAlgebraModule(A)
            sage: Psi = Matrix(QQ, [[1, 0, 0,   0],
            ....:                   [0, 0, 1,   0],
            ....:                   [0, 1, 0,   0],
            ....:                   [0, 0, 0, -17]])
            sage: X = TorsorPair(D, T, U, Psi)
            sage: K.<i> = QuadraticField(-1)
            sage: L.<a> = K.extension(x^4 - 17)
            sage: X.points(L)
            [(1, -i*a, -a^2, i*a^3),
             (1, i*a, -a^2, -i*a^3),
             (1, a, a^2, a^3),
             (1, -a, a^2, -a^3)]

        """
        return self.algebra().morphisms_to_ring(R)

    def splitting_field(self, names):
        """
        Return a splitting field for ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: from dual_pairs.torsor_pair import TorsorPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: T = FiniteFlatAlgebra(QQ, x^4 - 17)
            sage: U = FiniteFlatAlgebraModule(A)
            sage: Psi = Matrix(QQ, [[1, 0, 0,   0],
            ....:                   [0, 0, 1,   0],
            ....:                   [0, 1, 0,   0],
            ....:                   [0, 0, 0, -17]])
            sage: X = TorsorPair(D, T, U, Psi)
            sage: X.splitting_field('a')
            Number Field in a with defining polynomial x^8 + 68*x^6 + 1700*x^4 + 23120*x^2 + 73984

        """
        return self.algebra().splitting_field(names)

    def add(self, P, Q):
        """
        Return the sum of `P` and `Q`.

        INPUT:

        - `P` -- a point of the group scheme for which ``self`` is a
          torsor

        - `Q` -- a point of ``self``

        OUTPUT:

        The point `P + Q` of ``self``.

        EXAMPLES::

            sage: from dual_pairs import FiniteFlatAlgebra, DualPair
            sage: from dual_pairs.finite_flat_algebra_module import FiniteFlatAlgebraModule
            sage: from dual_pairs.torsor_pair import TorsorPair
            sage: R.<x> = QQ[]
            sage: A = FiniteFlatAlgebra(QQ, [x, x, x^2 + 17])
            sage: Phi = Matrix(QQ, [[1/4,  1/4,  1/2,   0],
            ....:                   [1/4,  1/4, -1/2,   0],
            ....:                   [1/2, -1/2,    0,   0],
            ....:                   [  0,    0,    0, -17]])
            sage: D = DualPair(A, Phi)
            sage: T = FiniteFlatAlgebra(QQ, x^4 - 17)
            sage: U = FiniteFlatAlgebraModule(A)
            sage: Psi = Matrix(QQ, [[1, 0, 0,   0],
            ....:                   [0, 0, 1,   0],
            ....:                   [0, 1, 0,   0],
            ....:                   [0, 0, 0, -17]])
            sage: X = TorsorPair(D, T, U, Psi)

            sage: K.<a> = NumberField(x^4 - 17)
            sage: o, p = D.points(K)
            sage: x, y = X.points(K)
            sage: o
            (1, 0, 0, 0)
            sage: p
            (0, 1, 0, 0)
            sage: x
            (1, a, a^2, a^3)
            sage: y
            (1, -a, a^2, -a^3)
            sage: X.add(o, x) == x
            True
            sage: X.add(o, y) == y
            True
            sage: X.add(p, x) == y
            True
            sage: X.add(p, y) == x
            True

            sage: R.<x> = QQ[]
            sage: L.<a> = QuadraticField(-1, 'i').extension(x^4 - 17)
            sage: o, p, q, r = D.points(L)
            sage: points_X = X.points(L)
            sage: p
            (0, 1, 0, 0)
            sage: points_X
            [(1, -i*a, -a^2, i*a^3),
             (1, i*a, -a^2, -i*a^3),
             (1, a, a^2, a^3),
             (1, -a, a^2, -a^3)]
            sage: [X.add(o, x) for x in points_X] == points_X
            True
            sage: [X.add(p, x) for x in points_X]
            [(1, i*a, -a^2, -i*a^3),
             (1, -i*a, -a^2, i*a^3),
             (1, -a, a^2, -a^3),
             (1, a, a^2, a^3)]
            sage: [X.add(q, x) for x in points_X]
            [(1, -a, a^2, -a^3),
             (1, a, a^2, a^3),
             (1, i*a, -a^2, -i*a^3),
             (1, -i*a, -a^2, i*a^3)]
            sage: [X.add(r, x) for x in points_X]
            [(1, a, a^2, a^3),
             (1, -a, a^2, -a^3),
             (1, -i*a, -a^2, i*a^3),
             (1, i*a, -a^2, -i*a^3)]
            sage: all(X.add(q, X.add(p, x)) == X.add(D.add(p, q), x) for x in points_X)
            True
        """
        R = P.base_ring()
        if Q.base_ring() is not R:
            raise ValueError("points have different base rings")
        D = self.dual_pair()
        B = D.algebra2().change_ring(R)
        U = self.dual_module().change_ring(B)
        S = B(P * D.theta()) * U(Q * self.upsilon())
        return self.psi() * S.module_element()
