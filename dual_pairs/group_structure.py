# -*- coding: utf-8 -*-
"""
Utility functions
"""

from __future__ import absolute_import

from sage.rings.all import QQ

def mod1(x):
    """
    Return the fractional part of `x`.
    """
    x = QQ(x)
    d = x.denominator()
    return (x.numerator() % d) / d

def find_perm(x, y):
    """
    Return the permutation that when applied to `x` gives `y`.
    """
    from sage.combinat.permutation import Permutation
    return Permutation([x.index(z) + 1 for z in y])

def standard_group_structure(d):
    r"""
    Return the standard Abelian group with the given structure.

    INPUT:

    - ``d`` -- list or tuple of integers :math:`(d_0, d_1, \ldots,
      d_{r-1})` with :math:`d_i` dividing :math:`d_{i-1}`

    OUTPUT:

    A pair ``(M, E)`` consisting of

    - ``M`` -- the finite Abelian group :math:`C_{d_0} \times C_{d_1}
      \times \ldots \times C_{d_{r-1}}`

    - ``E`` -- the matrix :math:`(\langle x,y\rangle)_{x\in M,y\in
      M^*}` of the canonical pairing :math:`M \times M^* \to
      \mathbf{Q}/\mathbf{Z}`, where `M` is ordered lexicographically
      and the dual group :math:`M^*` is identified with `M`, so that
      `E` is symmetric

    TESTS::

        sage: from dual_pairs.group_structure import standard_group_structure
        sage: standard_group_structure([3])
        (
                                                  [  0   0   0]
                                                  [  0 1/3 2/3]
        Additive abelian group isomorphic to Z/3, [  0 2/3 1/3]
        )
        sage: standard_group_structure([2, 2])
        (
                                                        [  0   0   0   0]
                                                        [  0 1/2   0 1/2]
                                                        [  0   0 1/2 1/2]
        Additive abelian group isomorphic to Z/2 + Z/2, [  0 1/2 1/2   0]
        )
    """
    from sage.groups.all import AdditiveAbelianGroup
    from sage.matrix.all import Matrix
    M = AdditiveAbelianGroup(d)
    L = [e.lift() for e in M]
    E = Matrix(QQ, [[mod1(sum(e1[k] * e2[k] / d[k] for k in range(len(d))))
                     for e2 in L] for e1 in L])
    return M, E

def find_group_structure(T):
    r"""
    Return the Abelian group structure with pairing matrix `T`.

    INPUT:

    - ``T`` -- a square matrix with rational entries in :math:`[0,1)`

    OUTPUT:

    A quadruple ``(M, E, p, q)`` consisting of

    - ``M`` -- a finite Abelian group :math:`C_{d_0} \times C_{d_1}
      \times \ldots \times C_{d_{r-1}}`

    - ``E`` -- the matrix of the standard pairing :math:`M \times M^*
      \to \mathbf{Q}/\mathbf{Z}`, where `M` is ordered
      lexicographically and the dual group :math:`M^*` is identified
      with `M`

    - ``p``, ``q`` -- permutations such that `E` is obtained by
      permuting the rows and columns of `T` according to `p` and `q`,
      respectively

    TESTS::

        sage: from dual_pairs.group_structure import find_group_structure, standard_group_structure
        sage: T = matrix([[0, 0], [0, 1/2]])
        sage: find_group_structure(T)
        (
                                                  [  0   0]
        Additive abelian group isomorphic to Z/2, [  0 1/2],
        [1, 2], [1, 2]
        )
        sage: T = matrix([[2/3, 1/3, 0], [0, 0, 0], [1/3, 2/3, 0]])
        sage: find_group_structure(T)
        (
                                                  [  0   0   0]
                                                  [  0 1/3 2/3]
        Additive abelian group isomorphic to Z/3, [  0 2/3 1/3],
        [2, 1, 3], [3, 2, 1]
        )

        sage: T = matrix([[0, 0, 0, 0], [0, 1/2, 0, 1/2],
        ....:             [0, 0, 1/2, 1/2], [0, 1/2, 1/2, 0]])
        sage: find_group_structure(T)
        (
                                                        [  0   0   0   0]
                                                        [  0 1/2   0 1/2]
                                                        [  0   0 1/2 1/2]
        Additive abelian group isomorphic to Z/2 + Z/2, [  0 1/2 1/2   0],
        [1, 3, 2, 4], [1, 3, 2, 4]
        )

    A random example::

        sage: d = [8, 4, 2]
        sage: n = prod(d)
        sage: S_n = SymmetricGroup(n)
        sage: M, E = standard_group_structure(d)
        sage: T = copy(E)
        sage: T.permute_rows(S_n.random_element())
        sage: T.permute_columns(S_n.random_element())
        sage: M1, E1, p, q = find_group_structure(T)
        sage: M1 == M
        True
        sage: E1 == E
        True
        sage: T.permute_rows(p)
        sage: T.permute_columns(q)
        sage: T == E
        True
    """
    import copy
    from sage.misc.all import exists, prod, sum
    d = []
    pivot_rows = []
    pivot_columns = []
    n = T.nrows()
    if T.ncols() != n:
        raise ValueError("not a square matrix")
    rows = list(range(n))
    columns = list(range(n))
    while len(rows) > 1:
        T1 = T.matrix_from_rows_and_columns(rows, columns)
        d1 = T1.denominator()
        t, i1 = exists(range(T1.nrows()),
                       lambda i: T1.row(i).denominator() == d1)
        if not t:
            raise ValueError("inconsistent data (no generator found)")
        j1 = list(T1.row(i1)).index(QQ((1, d1)))
        i0 = rows[i1]
        j0 = columns[j1]
        d.append(d1)
        pivot_rows.append(i0)
        pivot_columns.append(j0)
        rows = [i for i in rows if not T[i, j0]]
        columns = [j for j in columns if not T[i0, j]]
    if prod(d) != n:
        raise ValueError("inconsistent data")
    T = copy.copy(T)
    M, E = standard_group_structure(d)
    rows = [sum(e.lift()[k] * T.row(pivot_rows[k])
                for k in range(len(d))).apply_map(mod1) for e in M]
    p = find_perm(T.rows(), rows)
    T.permute_rows(p)
    columns = [sum(e.lift()[k] * T.column(pivot_columns[k])
                   for k in range(len(d))).apply_map(mod1) for e in M]
    q = find_perm(T.columns(), columns)
    T.permute_columns(q)
    if T != E:
        raise ValueError("inconsistent data")
    return M, E, p, q

def find_group_structure_old(T):
    """
    Old version of :func:`find_group_structure` (much slower, useless
    except maybe for debugging).
    """
    from sage.matrix.all import Matrix
    from sage.misc.all import prod
    Tp = T.__pari__()
    B = Tp.matrixqz(-1)
    C = Tp.matinverseimage(B).concat(Tp.matker()).matrixqz(-1)
    [u, v, d] = C.matsnf(5)
    U = (Tp * C * v * ~d).sage()
    d = tuple(d[i, i] for i in range(len(d)))
    if prod(d) != T.nrows():
        raise ValueError("inconsistent data")
    M, E = standard_group_structure(d)
    V = Matrix(QQ, [U * e.vector() for e in M]).transpose().apply_map(mod1, QQ)
    p = find_perm(V.rows(), E.rows())
    T.permute_rows(p)
    q = find_perm(T.columns(), E.columns())
    T.permute_columns(q)
    if T != E:
        raise ValueError("inconsistent data")
    return M, E, p, q
