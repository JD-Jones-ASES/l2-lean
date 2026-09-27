#!/usr/bin/env python3
"""Cross-check the finite content of the two-fold Langford theorem with the standard library.

An m-fold Langford sequence of order l and defect d reads the positions 1, ..., 2ml; every p in
[d, d + l - 1] occupies the endpoints of m pairwise disjoint pairs {a, a + p}. This script
recomputes, in plain Python with exact integers and no dependence on the Lean development:

  * the sixteen literal two-fold certificates (l <= 4) and the eleven literal solutions of the
    signed-permutation problem SP, from the definitions;
  * every block-reversal family at every cell of its domain with l <= 120, as a solution of SP and
    lifted through Lemma S to a two-fold sequence; the reversal and tau_l; the band coverage;
  * the cone (Theorem R) and the induction on l, replayed for small l;
  * the m-fold tight line for m <= 6 and odd l <= 21;
  * the row l = 1 for m <= 12 against d | m, and the cell (6, 3) at m = 3, by exhaustive search;
  * the residue bound, the forced-endpoint bound and the rigidity of the counting bound against
    exhaustive search on small cells, the cells (3m - 3, 3) and (2m - 1, 2) for m <= 200, both
    bounds at m = 2 for l <= 40, and one cell that the residue bound rejects;
  * two controls whose failure is the expected outcome.

The family tables below are transcribed from the Lean definitions in L2/FamR0a.lean,
L2/FamR0b.lean, L2/FamR1.lean, L2/FamR2.lean and L2/FamR3.lean (the rows in source order and the
domain hypotheses of each fam<Name>_sp theorem). Python 3.9 or later, standard library only. Run
from anywhere:

    python scripts/check_langford.py
"""

import sys
import time

failures = []


def report(ok, line):
    """Print one check and remember a failure."""
    print(("ok    " if ok else "FAIL  ") + line)
    if not ok:
        failures.append(line)


def interval(a, b):
    """The integers a, ..., b as a set."""
    return set(range(a, b + 1))


# ---------------------------------------------------------------------------------------------
# The definition (Challenge.lean) and the certificates (L2/Multi.lean)
# ---------------------------------------------------------------------------------------------

def is_langford(m, d, l, s, left_ends):
    """Langford.IsLangford m d l s, with the sets A of the second clause given as a witness.

    s maps each position 1, ..., 2ml to its entry; left_ends[p] is the set A for p.
    """
    n = 2 * m * l
    for i in range(1, n + 1):
        if not (d <= s.get(i, -1) < d + l):
            return False
    for p in range(d, d + l):
        a_set = left_ends.get(p, set())
        if len(a_set) != m:
            return False
        for a in a_set:
            if not (1 <= a and a + p <= n and a + p not in a_set):
                return False
        for i in range(1, n + 1):
            if (s[i] == p) != (i in a_set or (i - p) in a_set):
                return False
    return True


def endpoints(pairs):
    """pairEndpoints: the positions occupied by a set of pairs."""
    out = set()
    for a, b in pairs:
        out.add(a)
        out.add(b)
    return out


def differences(pairs):
    """pairDifferences: the differences b - a of a set of pairs."""
    return {b - a for a, b in pairs}


def is_multi_pairing(m, d, l, colours):
    """MultiPairing m d l C for the colours C 0, ..., C (m - 1)."""
    colours = [set(c) for c in colours]
    if len(colours) != m or d < 1 or l < 1:
        return False
    if any(differences(c) != interval(d, d + l - 1) for c in colours):
        return False
    union = set().union(*colours) if colours else set()
    if endpoints(union) != interval(1, 2 * m * l):
        return False
    return sum(len(c) for c in colours) <= m * l


def is_two_fold(d, l, a_pairs, b_pairs):
    """TwoFold d l A B."""
    a_pairs, b_pairs = set(a_pairs), set(b_pairs)
    return (d >= 1 and l >= 1
            and differences(a_pairs) == interval(d, d + l - 1)
            and differences(b_pairs) == interval(d, d + l - 1)
            and endpoints(a_pairs | b_pairs) == interval(1, 4 * l)
            and len(a_pairs) <= l and len(b_pairs) <= l)


def bridge(m, d, l, colours):
    """The sequence of a certificate (toSeq) and the check that it is an m-fold sequence."""
    pairs = set().union(*[set(c) for c in colours])
    s = {}
    for a, b in pairs:
        s[a] = b - a
        s[b] = b - a
    left = {}
    for a, b in pairs:
        left.setdefault(b - a, set()).add(a)
    return is_langford(m, d, l, s, left)


def search(m, d, l, first_only=True):
    """Every m-fold sequence of order l and defect d, by leftmost-first exhaustive search.

    The leftmost free position is always a left end, so each branch places one pair there.
    Returns (list of solutions as pair lists, number of nodes).
    """
    n = 2 * m * l
    used = [False] * (n + 2)
    left = {p: m for p in range(d, d + l)}
    pairs, sols, nodes = [], [], [0]

    def rec(i):
        nodes[0] += 1
        while i <= n and used[i]:
            i += 1
        if i > n:
            sols.append(list(pairs))
            return first_only
        for p in range(d, d + l):
            j = i + p
            if left[p] and j <= n and not used[j]:
                used[i] = used[j] = True
                left[p] -= 1
                pairs.append((i, j))
                if rec(i + 1):
                    return True
                pairs.pop()
                left[p] += 1
                used[i] = used[j] = False
        return False

    rec(1)
    return sols, nodes[0]


# ---------------------------------------------------------------------------------------------
# The signed-permutation problem (L2/Rows.lean, L2/SP.lean) and Lemma S (L2/LemmaS.lean)
# ---------------------------------------------------------------------------------------------

def row(a, c, n):
    """The row of n arrows a + r -> c + n + 1 - r, 1 <= r <= n (empty when n <= 0)."""
    return {(a + r, c + n + 1 - r) for r in range(1, n + 1)}


def is_sp(l, delta, graph):
    """SP l delta G: sources and targets [1, l], at most l arrows, values and mirrors [1 - l, l]."""
    graph = set(graph)
    values = {t - w + delta for w, t in graph}
    mirrors = {w - t + 1 - delta for w, t in graph}
    return (l >= 1
            and {w for w, _ in graph} == interval(1, l)
            and {t for _, t in graph} == interval(1, l)
            and values | mirrors == interval(1 - l, l)
            and len(graph) <= l)


def colour_a(delta, l, graph):
    """The outer pairs (l + 1 - w, 2l + t - w + delta)."""
    return {(l + 1 - w, 2 * l + t - w + delta) for w, t in graph}


def colour_b(delta, l, graph):
    """The inner pairs (2l + w - t + 1 - delta, 3l + w)."""
    return {(2 * l + w - t + 1 - delta, 3 * l + w) for w, t in graph}


def lift(l, delta, graph):
    """Lemma S: the two colours of the two-fold sequence of order l and defect l + delta."""
    return colour_a(delta, l, graph), colour_b(delta, l, graph)


def lift_ok(l, delta, graph):
    """The lift is a two-fold certificate and its sequence is a two-fold Langford sequence."""
    a_pairs, b_pairs = lift(l, delta, graph)
    d = l + delta
    return is_two_fold(d, l, a_pairs, b_pairs) and bridge(2, d, l, [a_pairs, b_pairs])


def tau_graph(l):
    """tau_l: reverse [1, (l + 1)/2] and [(l + 3)/2, l]."""
    h = (l + 1) // 2
    return row(0, 0, h) | row(h, h, (l - 1) // 2)


def swap(graph):
    """The inverse permutation."""
    return {(t, w) for w, t in graph}


def cinv_graph(n, delta, graph):
    """cinvGraph: shift the targets by mu = 2 delta - 1, append tau_mu on [n + 1, n + mu], invert."""
    mu = 2 * delta - 1
    step = {(w, t + mu) for w, t in graph} | {(w + n, t) for w, t in tau_graph(mu)}
    return swap(step)


# ---------------------------------------------------------------------------------------------
# The block-reversal families, transcribed from L2/Fam*.lean
# ---------------------------------------------------------------------------------------------

class Family:
    """fam<Name>: its rows (a, c, n) in source order, its order l, its delta and its domain."""

    def __init__(self, name, module, params, order, delta, rows, domain):
        self.name, self.module, self.params = name, module, params
        self.order, self.delta, self.rows, self.domain = order, delta, rows, domain

    def graph(self, *args):
        out = set()
        for a, c, n in self.rows(*args):
            out |= row(a, c, n)
        return out


FAMILIES = [
    Family(
        "A1", "L2/FamR0a.lean", ('q', 's',),
        order=lambda q, s: 4 * q,
        delta=lambda q, s: 2 * s + 1,
        rows=lambda q, s: [
            (0, 4 * q - 3 * s - 1, s),
            (s, 4 * q - s - 1, 1),
            (s + 1, 3 * q - 2 * s - 1, q - s),
            (q + 1, 1, 2 * s + 1 - q),
            (2 * s + 2, 4 * q - s, s),
            (3 * s + 2, 4 * q - 2 * s - 1, s),
            (4 * s + 2, 2 * s + 2 - q, 3 * q - 4 * s - 2),
            (3 * q, 2 * q - 2 * s, q - 1),
            (4 * q - 1, 0, 1),
        ],
        domain=lambda q, s: ((q <= 2 * s) and (q <= 2 * s + 1) and (1 <= s) and (s + 1 <= q) and
            (s + 1 <= q) and (2 <= q) and (1 <= q) and (1 <= q) and (s + 1 <= 2 * q) and
            (s + 1 <= 2 * q) and (s <= 2 * q) and (4 * s + 3 <= 3 * q)),
    ),
    Family(
        "A3", "L2/FamR0a.lean", ('q', 's',),
        order=lambda q, s: 4 * q,
        delta=lambda q, s: 2 * s + 2,
        rows=lambda q, s: [
            (0, 4 * q - 3 * s - 3, s + 1),
            (s + 1, 4 * q - s - 1, 1),
            (s + 2, 3 * q - 2 * s - 2, q - s - 1),
            (q + 1, 1, 2 * s + 2 - q),
            (2 * s + 3, 4 * q - s, s),
            (3 * s + 3, 4 * q - 2 * s - 2, s + 1),
            (4 * s + 4, 2 * s + 3 - q, 3 * q - 4 * s - 4),
            (3 * q, 2 * q - 2 * s - 1, q - 1),
            (4 * q - 1, 0, 1),
        ],
        domain=lambda q, s: ((q <= 2 * s + 1) and (q <= 2 * s + 2) and (1 <= s) and (0 <= s) and
            (s + 2 <= q) and (s + 1 <= q) and (2 <= q) and (1 <= q) and (1 <= q) and
            (s + 2 <= 2 * q) and (s + 1 <= 2 * q) and (s + 1 <= 2 * q) and (4 * s + 5 <= 3 * q)),
    ),
    Family(
        "U1", "L2/FamR0a.lean", ('q', 's',),
        order=lambda q, s: 4 * q,
        delta=lambda q, s: 4 * s + 1,
        rows=lambda q, s: [
            (0, 3 * q - 3 * s - 1, q - s),
            (q - s, 2 * q - 4 * s, 3 * s - q),
            (2 * s, 4 * q - 4 * s - 1, 2 * s + 1),
            (4 * s + 1, q - s, q - s),
            (q + 3 * s + 1, 2 * q - 2 * s, q - s - 1),
            (2 * q + 2 * s, 0, 1),
            (2 * q + 2 * s + 1, 4 * q - 2 * s, 2 * s),
            (2 * q + 4 * s + 1, 1, 2 * q - 4 * s - 1),
        ],
        domain=lambda q, s: ((q + 1 <= 3 * s) and (1 <= s) and (0 <= s) and (0 <= s) and
            (2 * s + 1 <= q) and (s + 2 <= q) and (s + 1 <= q) and (s + 1 <= q) and
            (s + 1 <= q) and (s <= q) and (s <= q) and (0 <= q + s)),
    ),
    Family(
        "U3", "L2/FamR0a.lean", ('q', 's',),
        order=lambda q, s: 4 * q,
        delta=lambda q, s: 4 * s + 2,
        rows=lambda q, s: [
            (0, 2 * q - 4 * s - 1, 2 * s),
            (2 * s, 4 * q - 4 * s - 3, 2 * s + 1),
            (4 * s + 1, 3 * q + s, q - s),
            (q + 3 * s + 1, 2 * q - 2 * s - 1, q - s - 3),
            (2 * q + 2 * s - 2, 4 * q - 4 * s - 4, 1),
            (2 * q + 2 * s - 1, 0, 1),
            (2 * q + 2 * s, 3 * q - 3 * s - 4, q - s),
            (3 * q + s, 4 * q - 2 * s - 2, 3 * s + 2 - q),
            (2 * q + 4 * s + 2, 1, 2 * q - 4 * s - 2),
        ],
        domain=lambda q, s: ((q <= 3 * s + 1) and (1 <= s) and (0 <= s) and (0 <= s) and
            (2 * s + 2 <= q) and (s + 4 <= q) and (s + 2 <= q) and (s + 2 <= q) and
            (s + 1 <= q) and (s + 1 <= q) and (s <= q) and (0 <= q + s)),
    ),
    Family(
        "U5", "L2/FamR0b.lean", ('q', 's',),
        order=lambda q, s: 4 * q,
        delta=lambda q, s: 4 * s + 3,
        rows=lambda q, s: [
            (0, 2 * q - 4 * s - 2, 2 * s + 1),
            (2 * s + 1, 4 * q - 4 * s - 3, 2 * s + 2),
            (4 * s + 3, 3 * q + s + 1, q - s - 1),
            (q + 3 * s + 2, 2 * q - 2 * s - 1, q - s - 1),
            (2 * q + 2 * s + 1, 0, 1),
            (2 * q + 2 * s + 2, 3 * q - 3 * s - 2, q - s - 1),
            (3 * q + s + 1, 4 * q - 2 * s - 1, 3 * s + 2 - q),
            (2 * q + 4 * s + 3, 1, 2 * q - 4 * s - 3),
        ],
        domain=lambda q, s: ((q <= 3 * s + 1) and (0 <= s) and (0 <= s) and (0 <= s) and
            (2 * s + 2 <= q) and (s + 2 <= q) and (s + 1 <= q) and (s + 1 <= q) and
            (s + 1 <= q) and (s <= q) and (0 <= q + s + 1)),
    ),
    Family(
        "U7", "L2/FamR0b.lean", ('q', 's',),
        order=lambda q, s: 4 * q,
        delta=lambda q, s: 4 * s + 4,
        rows=lambda q, s: [
            (0, 4 * q - 5 * s - 4, s + 1),
            (s + 1, 0, s + 1),
            (2 * s + 2, 4 * q - 7 * s - 6, s + 1),
            (3 * s + 3, 2 * q + s + 1, 2 * q - 2 * s - 2),
            (2 * q + s + 1, 4 * q - 6 * s - 5, 5 * s + 4 - 2 * q),
            (6 * s + 5, 4 * q - s - 1, s + 1),
            (7 * s + 6, s + 1, 4 * q - 8 * s - 7),
            (4 * q - s - 1, 2 * q - s - 1, 2 * q - 4 * s - 3),
            (6 * q - 5 * s - 4, 4 * q - 4 * s - 3, 5 * s + 4 - 2 * q),
        ],
        domain=lambda q, s: ((2 * q <= 5 * s + 3) and (2 * q <= 5 * s + 4) and (0 <= s) and
            (0 <= s + 1) and (2 * s + 2 <= q) and (2 * s + 2 <= q) and (s + 2 <= q) and
            (s + 1 <= q) and (3 * s + 3 <= 2 * q) and (s + 1 <= 2 * q)),
    ),
    Family(
        "V", "L2/FamR0b.lean", ('q', 's',),
        order=lambda q, s: 4 * q,
        delta=lambda q, s: 2 * s + 2,
        rows=lambda q, s: [
            (0, q - s - 1, q - s),
            (q - s, 5 * q - 4 * s - 2, s),
            (q, 5 * q - 3 * s - 2, s + 1),
            (q + s + 1, 3 * q - 2 * s - 1, 4 * q - 5 * s - 2),
            (5 * q - 4 * s - 1, 7 * q - 7 * s - 3, 3 * s + 1 - 2 * q),
            (3 * q - s, 2 * q - 2 * s - 1, 5 * s + 2 - 3 * q),
            (4 * s + 2, 5 * q - 2 * s - 1, 2 * s + 1 - q),
            (6 * s + 3 - q, 3 * s + 1 - q, 4 * q - 5 * s - 2),
            (3 * q + s + 1, 0, q - s - 1),
        ],
        domain=lambda q, s: ((3 * q <= 5 * s + 1) and (2 * q <= 3 * s) and (2 * q <= 3 * s) and
            (2 * q <= 3 * s + 1) and (q <= 2 * s) and (q <= 2 * s + 1) and (1 <= s) and
            (0 <= s) and (0 <= s) and (s + 2 <= q) and (s + 1 <= q) and (s + 1 <= q) and
            (0 <= q) and (s + 1 <= 2 * q) and (s <= 2 * q) and (s + 1 <= q) and
            (5 * s + 3 <= 4 * q)),
    ),
    Family(
        "T", "L2/FamR0b.lean", ('q', 's',),
        order=lambda q, s: 4 * q,
        delta=lambda q, s: 4 * s + 2,
        rows=lambda q, s: [
            (0, 4 * q - 6 * s - 2, 2 * s + 1),
            (2 * s + 1, 4 * q - 3 * s - 1, s),
            (3 * s + 1, 0, 4 * q - 7 * s - 2),
            (4 * q - 4 * s - 1, 4 * q - 7 * s - 2, 9 * s + 3 - 4 * q),
            (5 * s + 2, 4 * q - 4 * s - 1, s),
            (6 * s + 2, 4 * q - 2 * s - 1, 2 * s + 1),
            (8 * s + 3, 2 * s + 1, 4 * q - 8 * s - 3),
        ],
        domain=lambda q, s: ((4 * q <= 9 * s + 2) and (2 * q <= 5 * s + 2) and (1 <= s) and
            (0 <= s) and (2 * s + 1 <= q) and (2 * s + 1 <= q) and (s + 1 <= q) and
            (3 * s + 2 <= 2 * q) and (3 * s + 1 <= 2 * q) and (3 * s + 1 <= 2 * q) and
            (s <= 2 * q) and (7 * s + 3 <= 4 * q)),
    ),
    Family(
        "FA1", "L2/FamR1.lean", ('q', 's',),
        order=lambda q, s: 4 * q + 1,
        delta=lambda q, s: 2 * s + 1,
        rows=lambda q, s: [
            (0, 4 * q - 3 * s, s),
            (s, 2 * q - 2 * s, s - 1),
            (2 * s - 1, 3 * q, q),
            (q + 2 * s - 1, 2 * q - s - 1, q - s),
            (2 * q + s - 1, 3 * q - 2 * s - 1, q + 1 - s),
            (3 * q, 4 * q - 2 * s, 2 * s - q),
            (2 * q + 2 * s, 4 * q, 1),
            (2 * q + 2 * s + 1, 0, 2 * q - 2 * s),
        ],
        domain=lambda q, s: (q + 1 <= 2 * s) and (s + 1 <= q),
    ),
    Family(
        "FA3", "L2/FamR1.lean", ('q', 's',),
        order=lambda q, s: 4 * q + 1,
        delta=lambda q, s: 2 * s + 2,
        rows=lambda q, s: [
            (0, 4 * q - 3 * s - 1, s + 1),
            (s + 1, 2 * q - 2 * s - 1, s + 1),
            (2 * s + 2, 3 * q + 1, q),
            (q + 2 * s + 2, 2 * q - s, q - s - 1),
            (2 * q + s + 1, 3 * q - 2 * s - 1, q - s),
            (3 * q + 1, 4 * q - 2 * s, 2 * s + 1 - q),
            (2 * q + 2 * s + 2, 0, 2 * q - 2 * s - 1),
        ],
        domain=lambda q, s: (q <= 2 * s) and (s + 2 <= q),
    ),
    Family(
        "FT", "L2/FamR1.lean", ('q',),
        order=lambda q: 4 * q + 1,
        delta=lambda q: 2 * q,
        rows=lambda q: [
            (0, q + 1, q),
            (q, 1, q - 1),
            (2 * q - 1, 3 * q + 1, q),
            (3 * q - 1, q, 1),
            (3 * q, 2 * q + 1, q),
            (4 * q, 0, 1),
        ],
        domain=lambda q: (2 <= q),
    ),
    Family(
        "FL1", "L2/FamR1.lean", ('p',),
        order=lambda p: 8 * p + 1,
        delta=lambda p: 2 * p + 1,
        rows=lambda p: [
            (0, 2 * p, 1),
            (1, 5 * p + 1, p),
            (p + 1, 2 * p + 1, p - 1),
            (2 * p, 6 * p + 1, 2 * p),
            (4 * p, 3 * p, p),
            (5 * p, 4 * p, p + 1),
            (6 * p + 1, 0, 2 * p),
        ],
        domain=lambda p: (2 <= p),
    ),
    Family(
        "FL5", "L2/FamR1.lean", ('p',),
        order=lambda p: 8 * p + 5,
        delta=lambda p: 2 * p + 2,
        rows=lambda p: [
            (0, 5 * p + 3, p + 1),
            (p + 1, 2 * p + 1, p + 1),
            (2 * p + 2, 6 * p + 4, 2 * p + 1),
            (4 * p + 3, 3 * p + 2, p),
            (5 * p + 3, 4 * p + 2, p + 1),
            (6 * p + 4, 0, 2 * p + 1),
        ],
        domain=lambda p: (1 <= p),
    ),
    Family(
        "FA", "L2/FamR2.lean", ('q', 'h',),
        order=lambda q, h: 4 * q + 2,
        delta=lambda q, h: h,
        rows=lambda q, h: [
            (0, 4 * q + 3 - 2 * h, h - 1),
            (h - 1, 3 * q + 1, q + 1),
            (q + h, 0, 3 * q + 3 - 2 * h),
            (4 * q + 3 - h, 3 * q + 3 - 2 * h, q),
            (5 * q + 3 - h, 4 * q + 2 - h, h - q - 1),
        ],
        domain=lambda q, h: (q + 2 <= h) and (2 * h <= 3 * q + 2),
    ),
    Family(
        "FB2", "L2/FamR2.lean", ('k', 'h',),
        order=lambda k, h: 8 * k + 2,
        delta=lambda k, h: h,
        rows=lambda k, h: [
            (0, 9 * k + 3 - 2 * h, h - k - 1),
            (h - k - 1, 0, k),
            (h - 1, 5 * k + 1, 3 * k + 1),
            (3 * k + h, k, 8 * k + 3 - 2 * h),
            (11 * k + 3 - h, 8 * k + 2 - h, h - 3 * k - 1),
        ],
        domain=lambda k, h: (1 <= k) and (3 * k + 2 <= h) and (h <= 4 * k + 1),
    ),
    Family(
        "FB6", "L2/FamR2.lean", ('k', 'h',),
        order=lambda k, h: 8 * k + 6,
        delta=lambda k, h: h,
        rows=lambda k, h: [
            (0, 9 * k + 8 - 2 * h, h - k - 1),
            (h - k - 1, 0, k + 1),
            (h, 5 * k + 4, 3 * k + 2),
            (3 * k + h + 2, k + 1, 8 * k + 7 - 2 * h),
            (11 * k + 9 - h, 8 * k + 7 - h, h - 3 * k - 3),
        ],
        domain=lambda k, h: (3 * k + 4 <= h) and (h <= 4 * k + 3),
    ),
    Family(
        "F4", "L2/FamR2.lean", ('k',),
        order=lambda k: 8 * k + 6,
        delta=lambda k: 3 * k + 3,
        rows=lambda k: [
            (0, 2 * k + 1, 3 * k + 2),
            (3 * k + 2, 6 * k + 4, 2 * k + 2),
            (5 * k + 4, 0, 2 * k + 1),
            (7 * k + 5, 5 * k + 3, k + 1),
        ],
        domain=lambda k: (0 <= k),
    ),
    Family(
        "R3O", "L2/FamR3.lean", ('q', 'u',),
        order=lambda q, u: 4 * q + 3,
        delta=lambda q, u: 2 * q + 1 - 2 * u,
        rows=lambda q, u: [
            (0, q + 3 * u + 2, q - u),
            (q - u, 2 * u + 1, q - u),
            (2 * q - 2 * u, 3 * q + 2, q + 1),
            (3 * q + 1 - 2 * u, q + u + 1, u),
            (3 * q + 1 - u, q + 2 * u + 1, u + 1),
            (3 * q + 2, 2 * q + 2 * u + 2, q - 2 * u),
            (4 * q + 2 - 2 * u, 0, 2 * u + 1),
        ],
        domain=lambda q, u: (1 <= u) and (2 * u + 1 <= q),
    ),
    Family(
        "R3E", "L2/FamR3.lean", ('q', 'u',),
        order=lambda q, u: 4 * q + 3,
        delta=lambda q, u: 2 * q + 2 - 2 * u,
        rows=lambda q, u: [
            (0, 2 * u, 1),
            (1, q + 3 * u + 2, q + 1 - u),
            (q + 2 - u, 2 * u + 1, q - u),
            (2 * q + 2 - 2 * u, 3 * q + 3, q),
            (3 * q + 2 - 2 * u, q + u + 1, u),
            (3 * q + 2 - u, q + 2 * u + 1, u + 1),
            (3 * q + 3, 2 * q + 2 * u + 3, q - 2 * u),
            (4 * q + 3 - 2 * u, 0, 2 * u),
        ],
        domain=lambda q, u: (1 <= u) and (2 * u + 1 <= q),
    ),
    Family(
        "R3Q", "L2/FamR3.lean", ('q', 'u',),
        order=lambda q, u: 4 * q + 3,
        delta=lambda q, u: 2 * q + 2 - 2 * u,
        rows=lambda q, u: [
            (0, 2 * u, 2 * q + 1 - 4 * u),
            (2 * q + 1 - 4 * u, 3 * q + 2 - u, q + 1 - u),
            (3 * q + 2 - 5 * u, 2 * q + 1 - 2 * u, 3 * u - q),
            (2 * q + 2 - 2 * u, 4 * q + 3 - 2 * u, 2 * u),
            (2 * q + 2, q + u + 1, q - u),
            (3 * q + 2 - u, 2 * q + 1, q + 1 - u),
            (4 * q + 3 - 2 * u, 0, 2 * u),
        ],
        domain=lambda q, u: (q + 1 <= 3 * u) and (2 * u <= q),
    ),
    Family(
        "R3T1", "L2/FamR3.lean", ('q',),
        order=lambda q: 4 * q + 3,
        delta=lambda q: 2 * q + 1,
        rows=lambda q: [
            (0, q + 2, q),
            (q, 1, q),
            (2 * q, 3 * q + 2, q + 1),
            (3 * q + 1, q + 1, 1),
            (3 * q + 2, 2 * q + 2, q),
            (4 * q + 2, 0, 1),
        ],
        domain=lambda q: (1 <= q),
    ),
]

# The eleven literal solutions of L2/Literals.lean: (name, l, delta, graph).
SP_LITERALS = [
    ("sp_7_3", 7, 2, [(1, 6), (2, 4), (3, 7), (4, 3), (5, 5), (6, 2), (7, 1)]),
    ("sp_5_3", 5, 2, [(1, 3), (2, 5), (3, 2), (4, 4), (5, 1)]),
    ("sp_9_5", 9, 3, [(1, 6), (2, 5), (3, 9), (4, 8), (5, 1), (6, 7), (7, 4), (8, 3), (9, 2)]),
    ("sp_8_5", 8, 3, [(1, 2), (2, 6), (3, 8), (4, 7), (5, 5), (6, 4), (7, 3), (8, 1)]),
    ("sp_8_7", 8, 4, [(1, 1), (2, 5), (3, 4), (4, 8), (5, 7), (6, 2), (7, 6), (8, 3)]),
    ("sp_12_9", 12, 5, [(1, 7), (2, 6), (3, 5), (4, 1), (5, 12), (6, 11), (7, 10), (8, 4),
                        (9, 9), (10, 8), (11, 3), (12, 2)]),
    ("sp_12_11", 12, 6, [(1, 2), (2, 1), (3, 3), (4, 9), (5, 8), (6, 12), (7, 11), (8, 10),
                         (9, 7), (10, 6), (11, 5), (12, 4)]),
    ("sp_16_11", 16, 6, [(1, 1), (2, 4), (3, 12), (4, 11), (5, 10), (6, 16), (7, 15), (8, 14),
                         (9, 13), (10, 9), (11, 8), (12, 7), (13, 6), (14, 5), (15, 3), (16, 2)]),
    ("sp_20_15", 20, 8, [(1, 2), (2, 1), (3, 14), (4, 13), (5, 12), (6, 11), (7, 10), (8, 20),
                         (9, 19), (10, 18), (11, 17), (12, 16), (13, 15), (14, 7), (15, 6),
                         (16, 5), (17, 4), (18, 3), (19, 9), (20, 8)]),
    ("sp_24_17", 24, 9, [(1, 2), (2, 1), (3, 17), (4, 16), (5, 15), (6, 14), (7, 13), (8, 12),
                         (9, 24), (10, 23), (11, 22), (12, 21), (13, 20), (14, 19), (15, 18),
                         (16, 9), (17, 8), (18, 7), (19, 6), (20, 5), (21, 4), (22, 3), (23, 11),
                         (24, 10)]),
    ("sp_32_23", 32, 12, [(1, 2), (2, 1), (3, 23), (4, 22), (5, 21), (6, 20), (7, 19), (8, 18),
                          (9, 17), (10, 16), (11, 15), (12, 3), (13, 32), (14, 31), (15, 30),
                          (16, 29), (17, 28), (18, 27), (19, 26), (20, 25), (21, 24), (22, 11),
                          (23, 10), (24, 9), (25, 8), (26, 7), (27, 6), (28, 5), (29, 4),
                          (30, 14), (31, 13), (32, 12)]),
]

# The sixteen literal two-fold certificates of L2/Literals.lean: ((d, l), A, B).
TWO_FOLD_LITERALS = [
    ((1, 1), [(1, 2)], [(3, 4)]),
    ((2, 1), [(1, 3)], [(2, 4)]),
    ((1, 2), [(1, 2), (3, 5)], [(4, 6), (7, 8)]),
    ((2, 2), [(1, 3), (2, 5)], [(4, 7), (6, 8)]),
    ((3, 2), [(1, 4), (2, 6)], [(3, 7), (5, 8)]),
    ((1, 3), [(1, 2), (5, 7), (6, 9)], [(3, 4), (8, 11), (10, 12)]),
    ((2, 3), [(1, 4), (2, 6), (9, 11)], [(3, 7), (5, 8), (10, 12)]),
    ((3, 3), [(1, 4), (2, 6), (3, 8)], [(5, 10), (7, 11), (9, 12)]),
    ((4, 3), [(1, 5), (2, 7), (3, 9)], [(4, 10), (6, 11), (8, 12)]),
    ((5, 3), [(1, 8), (2, 7), (3, 9)], [(4, 10), (5, 12), (6, 11)]),
    ((1, 4), [(1, 4), (2, 3), (5, 7), (6, 10)], [(8, 11), (9, 13), (12, 14), (15, 16)]),
    ((2, 4), [(1, 3), (2, 7), (4, 8), (10, 13)], [(5, 9), (6, 11), (12, 15), (14, 16)]),
    ((3, 4), [(1, 5), (3, 8), (7, 13), (11, 14)], [(2, 6), (4, 9), (10, 16), (12, 15)]),
    ((4, 4), [(1, 5), (2, 7), (3, 9), (4, 11)], [(6, 13), (8, 14), (10, 15), (12, 16)]),
    ((5, 4), [(1, 6), (2, 8), (3, 10), (4, 12)], [(5, 13), (7, 14), (9, 15), (11, 16)]),
    ((6, 4), [(1, 7), (2, 11), (3, 10), (4, 12)], [(5, 13), (6, 15), (8, 14), (9, 16)]),
]

MAX_L = 120


def domain_cells(fam, max_l):
    """Every parameter tuple in the family's domain with order at most max_l."""
    cells = []
    rng = range(-2 * max_l, 2 * max_l + 1)
    if len(fam.params) == 1:
        for x in rng:
            if fam.domain(x) and fam.order(x) <= max_l:
                cells.append((x,))
    else:
        for x in rng:
            for y in rng:
                if fam.domain(x, y) and fam.order(x, y) <= max_l:
                    cells.append((x, y))
    return cells


# ---------------------------------------------------------------------------------------------
# The cone (L2/Cone.lean) and the induction (L2/Main.lean), replayed
# ---------------------------------------------------------------------------------------------

LITERAL_SP = {(l, 2 * delta - 1): set(g) for _, l, delta, g in SP_LITERALS}


def family_cell(l, mu):
    """A family whose domain contains the band cell (l, mu), with its graph, or None."""
    for fam in FAMILIES:
        for args in FAMILY_INDEX.get((fam.name, l), []):
            if 2 * fam.delta(*args) - 1 == mu:
                return fam.graph(*args)
    return None


def band_graph(l, mu):
    """A solution of SP(l, (mu + 1)/2) on the band l/2 < mu <= l, l >= 5, as Band.lean splits it."""
    if mu == l:
        return tau_graph(l)
    if (l, mu) in LITERAL_SP:
        return LITERAL_SP[(l, mu)]
    return family_cell(l, mu)


def cone_graph(l, delta):
    """A solution of SP(l, delta) on the cone -l <= 2 delta - 1 <= l, l >= 5, as Cone.lean builds it."""
    if delta < 1:
        g = cone_graph(l, 1 - delta)
        return None if g is None else swap(g)
    mu = 2 * delta - 1
    if mu == 1:
        return row(0, 0, l)
    if mu == l or l < 2 * mu:
        return band_graph(l, mu)
    lp = l - mu
    if lp == mu:
        base = tau_graph(mu)
    elif lp < 2 * mu and lp >= 5:
        base = band_graph(lp, mu)
    elif lp < 2 * mu:
        base = LITERAL_SP.get((lp + mu, mu)) if (lp, mu) == (4, 3) else None
        return base
    else:
        base = cone_graph(lp, delta)
    return None if base is None else cinv_graph(lp, delta, base)


def shift(c, pairs):
    """shiftPairs: translate every pair by c."""
    return {(a + c, b + c) for a, b in pairs}


LITERAL_TWO_FOLD = {dl: (set(a), set(b)) for dl, a, b in TWO_FOLD_LITERALS}


def two_fold_all(d, l, memo):
    """twoFold_all: a two-colour certificate for (d, l), 2d <= 3l + 1, by the induction of Main.lean."""
    if (d, l) in memo:
        return memo[(d, l)]
    if l <= 4:
        out = LITERAL_TWO_FOLD[(d, l)]
    elif l <= 2 * d - 1:
        g = cone_graph(l, d - l)
        out = None if g is None else lift(l, d - l, g)
    else:
        l1 = (2 * d + 1) // 3
        first = two_fold_all(d, l1, memo)
        second = two_fold_all(d + l1, l - l1, memo)
        if first is None or second is None:
            out = None
        else:
            out = (first[0] | shift(4 * l1, second[0]), first[1] | shift(4 * l1, second[1]))
    memo[(d, l)] = out
    return out


# ---------------------------------------------------------------------------------------------
# The tight line (L2/Tight.lean) and the row l = 1 (L2/OrderOne.lean)
# ---------------------------------------------------------------------------------------------

def table1(d0):
    """Table 1 of the source as pairs."""
    return ({(d0 - r, 2 * d0 + r) for r in range(0, d0)}
            | {(2 * d0 - 1 - r, 3 * d0 + r) for r in range(0, d0 - 1)})


def tight_colour(m, d0, c):
    """Colour c of the m-fold tight sequence of order l = 2 d0 - 1."""
    l = 2 * d0 - 1
    return {(a + c * l, b + (m - 1 + c) * l) for a, b in table1(d0)}


def order_one_colours(m, d):
    """m / d juxtaposed copies of the tight cell (d, 1) at multiplicity d (d divides m)."""
    colours = []
    for j in range(m // d):
        for c in range(d):
            colours.append(shift(2 * d * j, tight_colour(d, 1, c)))
    return colours


# ---------------------------------------------------------------------------------------------
# The bounds (L2/Residue.lean, L2/Forced.lean, L2/Straddle.lean), as pinned in Challenge.lean
# ---------------------------------------------------------------------------------------------

def tsub(a, b):
    """Subtraction on the natural numbers as Lean truncates it: a - b, and 0 when b > a."""
    return a - b if a >= b else 0


def counting_holds(m, d, l):
    """The counting bound of Langford.necessary: 2d + l <= 2ml + 1."""
    return 2 * d + l <= 2 * m * l + 1


def parity_holds(m, d, l):
    """The parity condition of Langford.necessary: for odd m, l(2d + l + 1) = 0 (mod 4)."""
    return m % 2 == 0 or (l * (2 * d + l + 1)) % 4 == 0


def residue_sides(m, d, l, t):
    """Langford.residue_bound at T = t: the two sides (ml % T)(T - ml % T) and
    m * sum_{i < l} ((d + i - T) + (T - (d + i))), with truncated subtraction."""
    r = (m * l) % t
    return r * tsub(t, r), m * sum(tsub(d + i, t) + tsub(t, d + i) for i in range(l))


def residue_holds(m, d, l, t):
    """The residue bound at T = t."""
    left, right = residue_sides(m, d, l, t)
    return left <= right


def forced_holds(m, d, l):
    """Langford.forced_endpoint: 6mld + ml <= 4d^2 + 2(ml)^2 + ml^2."""
    return 6 * m * l * d + m * l <= 4 * d * d + 2 * (m * l) * (m * l) + m * l * l


def straddles(m, l, pairs):
    """The right side of Langford.tight_iff_straddle: ml < i + s_i for every position i <= ml."""
    s = {}
    for a, b in pairs:
        s[a] = s[b] = b - a
    return all(m * l < i + s[i] for i in range(1, m * l + 1))


# ---------------------------------------------------------------------------------------------

FAMILY_INDEX = {}


def main():
    start = time.time()
    print("Two-fold Langford sequences: the finite content of the development.")

    print("")
    print("Literal certificates (L2/Literals.lean):")
    bad = [dl for dl, a, b in TWO_FOLD_LITERALS
           if not (is_two_fold(dl[0], dl[1], a, b) and bridge(2, dl[0], dl[1], [a, b]))]
    cells = {(d, l) for l in range(1, 5) for d in range(1, (3 * l + 1) // 2 + 1)}
    report(not bad and {dl for dl, _, _ in TWO_FOLD_LITERALS} == cells,
           f"the {len(TWO_FOLD_LITERALS)} two-fold certificates are exactly the in-bound cells with "
           "l <= 4, each a certificate and a two-fold sequence" + (f"; bad {bad}" if bad else ""))
    bad = [name for name, l, delta, g in SP_LITERALS if not (is_sp(l, delta, g) and lift_ok(l, delta, g))]
    report(not bad, f"the {len(SP_LITERALS)} literal SP solutions solve SP(l, delta) and lift through "
           "Lemma S" + (f"; bad {bad}" if bad else ""))

    print("")
    print(f"Block-reversal families (L2/Fam*.lean), every domain cell with l <= {MAX_L}:")
    total = 0
    for fam in FAMILIES:
        cells = domain_cells(fam, MAX_L)
        bad = []
        for args in cells:
            l, delta = fam.order(*args), fam.delta(*args)
            FAMILY_INDEX.setdefault((fam.name, l), []).append(args)
            g = fam.graph(*args)
            if not (is_sp(l, delta, g) and lift_ok(l, delta, g)):
                bad.append(args)
        total += len(cells)
        report(bool(cells) and not bad,
               f"{fam.name:5s} ({fam.module}): {len(cells)} domain cells, each solves SP and lifts to a "
               "two-fold sequence" + (f"; bad {bad[:5]}" if bad else ""))
    report(len(FAMILIES) == 21, f"21 families, {total} family cells in all")
    bad = [l for l in range(1, MAX_L + 1) if not (is_sp(l, 1, row(0, 0, l)) and lift_ok(l, 1, row(0, 0, l)))]
    report(not bad, f"the reversal solves SP(l, 1) and lifts, 1 <= l <= {MAX_L}")
    bad = [l for l in range(1, MAX_L + 1, 2)
           if not (is_sp(l, (l + 1) // 2, tau_graph(l)) and lift_ok(l, (l + 1) // 2, tau_graph(l)))]
    report(not bad, f"tau_l solves SP(l, (l + 1)/2) and lifts, odd l <= {MAX_L}")

    print("")
    print(f"The band (L2/Band.lean), l <= {MAX_L}:")
    sporadic = {(8, 5), (8, 7), (12, 9), (12, 11), (16, 11), (20, 15), (24, 17), (32, 23)}
    uncovered, band_cells = [], 0
    for l in range(5, MAX_L + 1):
        for mu in range(l // 2 + 1, l + 1):
            if mu % 2 == 1 and l < 2 * mu:
                band_cells += 1
                if mu != l and family_cell(l, mu) is None:
                    uncovered.append((l, mu))
    expected = sorted(sporadic | {(5, 3), (9, 5)})
    report(sorted(uncovered) == expected,
           f"of {band_cells} band cells, the ones in no family domain with mu < l are exactly the eight "
           "sporadic cells and the bases (5, 3), (9, 5)" + ("" if sorted(uncovered) == expected
                                                          else f"; found {sorted(uncovered)}"))

    print("")
    print("The cone and the induction (L2/Cone.lean, L2/Main.lean), replayed:")
    bad, count = [], 0
    for l in range(5, 61):
        for mu in range(-l, l + 1, 2) if l % 2 == 1 else range(-l + 1, l, 2):
            delta = (mu + 1) // 2
            g = cone_graph(l, delta)
            count += 1
            if g is None or not is_sp(l, delta, g):
                bad.append((l, mu))
    report(not bad, f"SP(l, delta) solved at every cone cell 5 <= l <= 60, -l <= 2 delta - 1 <= l: "
           f"{count} cells" + (f"; bad {bad[:5]}" if bad else ""))
    memo, bad, count = {}, [], 0
    for l in range(1, 41):
        for d in range(1, (3 * l + 1) // 2 + 1):
            cert = two_fold_all(d, l, memo)
            count += 1
            if cert is None or not (is_two_fold(d, l, *cert) and bridge(2, d, l, list(cert))):
                bad.append((d, l))
    report(not bad, f"a two-fold sequence at every in-bound cell with l <= 40: {count} cells"
           + (f"; bad {bad[:5]}" if bad else ""))
    bad = []
    for l in range(1, 6):
        for d in range(1, 2 * l + 4):
            sols, _ = search(2, d, l)
            if bool(sols) != (2 * d <= 3 * l + 1):
                bad.append((d, l))
    report(not bad, "exhaustive search, l <= 5, d <= 2l + 3: a two-fold sequence exists exactly when "
           "2d <= 3l + 1" + (f"; disagrees at {bad}" if bad else ""))

    print("")
    print("The m-fold statements (L2/Tight.lean, L2/OrderOne.lean, L2/SixThree.lean):")
    bad, count = [], 0
    for m in range(1, 7):
        for l in range(1, 22, 2):
            d0 = (l + 1) // 2
            d = m * l - (d0 - 1)
            colours = [tight_colour(m, d0, c) for c in range(m)]
            count += 1
            if not (2 * d + l == 2 * m * l + 1 and is_multi_pairing(m, d, l, colours)
                    and bridge(m, d, l, colours)):
                bad.append((m, d, l))
    report(not bad, f"tight line, m <= 6, odd l <= 21: {count} cells, each an m-fold sequence"
           + (f"; bad {bad}" if bad else ""))
    bad, count = [], 0
    for m in range(1, 13):
        for d in range(1, 2 * m + 1):
            sols, _ = search(m, d, 1)
            count += 1
            divides = m % d == 0
            if bool(sols) != divides:
                bad.append((m, d))
            if divides:
                colours = order_one_colours(m, d)
                if not (is_multi_pairing(m, d, 1, colours) and bridge(m, d, 1, colours)):
                    bad.append((m, d, "construction"))
    report(not bad, f"row l = 1, m <= 12, d <= 2m: {count} cells; a sequence exists exactly when d | m, "
           "and the juxtaposed construction is one" + (f"; bad {bad}" if bad else ""))
    sols, nodes = search(3, 6, 3, first_only=False)
    necessary = 2 * 6 + 3 <= 2 * 3 * 3 + 1 and (3 * (2 * 6 + 3 + 1)) % 4 == 0
    report(not sols and necessary,
           f"(d, l) = (6, 3) at m = 3 meets the necessary conditions and has no sequence: exhaustive "
           f"search, {nodes} nodes")
    bad = []
    for m in range(3, 13):
        if m == 3:
            d, l = 6, 3
        elif m % 2 == 0:
            d, l = m - 1, 1
        else:
            d, l = m - 2, 1
        nec = 2 * d + l <= 2 * m * l + 1 and (m % 2 == 0 or (l * (2 * d + l + 1)) % 4 == 0)
        if not nec or search(m, d, l)[0]:
            bad.append(m)
    report(not bad, "the witnesses of not_sufficient, 3 <= m <= 12, meet the necessary conditions and "
           "have no sequence" + (f"; bad {bad}" if bad else ""))

    print("")
    print("The bounds (L2/Residue.lean, L2/Forced.lean, L2/Straddle.lean):")
    grid = [(m, d, l) for m in range(1, 5) for l in range(1, 7) if 2 * m * l <= 20
            for d in range(1, (2 * m * l + 1 - l) // 2 + 2)]
    realized, count, bad_res, bad_forced, bad_rigid = [], 0, [], [], []
    for m, d, l in grid:
        sols, _ = search(m, d, l, first_only=False)
        if not sols:
            continue
        realized.append((m, d, l))
        count += len(sols)
        bad_res += [(m, d, l, t) for t in range(1, 2 * m * l + 3) if not residue_holds(m, d, l, t)]
        if not forced_holds(m, d, l):
            bad_forced.append((m, d, l))
        tight = 2 * d + l == 2 * m * l + 1
        bad_rigid += [(m, d, l) for pairs in sols if straddles(m, l, pairs) != tight]
    report(not bad_res, f"exhaustive search on the {len(grid)} cells with m <= 4, l <= 6, 2ml <= 20 and d "
           f"up to one past the counting line: at each of the {len(realized)} cells with a sequence the "
           "residue bound holds for every T in [1, 2ml + 2]"
           + (f"; fails at {bad_res[:5]}" if bad_res else ""))
    report(not bad_forced, f"the forced-endpoint bound holds at each of the {len(realized)} cells with a "
           "sequence" + (f"; fails at {bad_forced[:5]}" if bad_forced else ""))
    report(not bad_rigid, f"rigidity: each of the {count} sequences found has 2d + l = 2ml + 1 exactly when "
           "ml < i + s_i for every position i <= ml" + (f"; fails at {bad_rigid[:5]}" if bad_rigid else ""))
    top = range(3, 201)
    bad = [m for m in top if not (counting_holds(m, 3 * m - 3, 3) and parity_holds(m, 3 * m - 3, 3))
           or forced_holds(m, 3 * m - 3, 3) != (m == 3)]
    report(not bad, "(d, l) = (3m - 3, 3), 3 <= m <= 200: meets counting and parity, and fails the "
           "forced-endpoint bound exactly for m >= 4 (m = 3 is the cell (6, 3))"
           + (f"; bad {bad[:5]}" if bad else ""))
    bad = [m for m in top if not counting_holds(m, 2 * m - 1, 2) or forced_holds(m, 2 * m - 1, 2)
           or parity_holds(m, 2 * m - 1, 2) != (m % 2 == 0)]
    report(not bad, "(d, l) = (2m - 1, 2), 3 <= m <= 200: meets counting (and parity exactly for even m), "
           "and fails the forced-endpoint bound" + (f"; bad {bad[:5]}" if bad else ""))
    bad, count = [], 0
    for l in range(1, 41):
        for d in range(1, (3 * l + 1) // 2 + 1):
            count += 1
            if not (forced_holds(2, d, l) and all(residue_holds(2, d, l, t) for t in range(1, 4 * l + 3))):
                bad.append((d, l))
    report(not bad, f"m = 2: the residue bound (every T <= 4l + 2) and the forced-endpoint bound hold at "
           f"every in-bound cell with l <= 40: {count} cells" + (f"; fail at {bad[:5]}" if bad else ""))
    left, right = residue_sides(7, 9, 4, 11)
    report(not residue_holds(7, 9, 4, 11) and (left, right) == (30, 28)
           and counting_holds(7, 9, 4) and parity_holds(7, 9, 4),
           f"control: the residue bound rejects (m, d, l) = (7, 9, 4) at T = 11 (right side {right} < left "
           f"side {left}), a cell that meets counting and parity, as it must")

    print("")
    print("Controls:")
    fam = FAMILIES[0]
    args = domain_cells(fam, MAX_L)[0]
    rows = fam.rows(*args)
    (a0, c0, n0), (a1, c1, n1) = rows[0], rows[1]
    mutated = set(row(a0, c1, n0)) | set(row(a1, c0, n1))
    for a, c, n in rows[2:]:
        mutated |= row(a, c, n)
    l, delta = fam.order(*args), fam.delta(*args)
    report(not is_sp(l, delta, mutated),
           f"control: {fam.name} at {args} with the target starts of its first two blocks exchanged "
           "does not solve SP, as it must not")
    a_pairs, b_pairs = lift(7, 2, set(SP_LITERALS[0][3]))
    (x0, y0), (x1, y1) = sorted(a_pairs)[:2]
    broken = (a_pairs - {(x0, y0), (x1, y1)}) | {(x0, y1), (x1, y0)}
    report(not (is_two_fold(9, 7, broken, b_pairs) or bridge(2, 9, 7, [broken, b_pairs])),
           "control: the lift of sp_7_3 with the right ends of two pairs exchanged is not a two-fold "
           "sequence of order 7 and defect 9, as it must not be")

    print("")
    print(f"elapsed {time.time() - start:.1f} s")
    if failures:
        print(f"{len(failures)} CHECK(S) FAILED")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
