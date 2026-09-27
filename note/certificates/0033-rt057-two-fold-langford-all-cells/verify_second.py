#!/usr/bin/env python3
"""
verify_second.py -- a second, independent construction of a two-fold Langford sequence at every in-bound cell (standalone, stdlib only).

A two-fold Langford sequence of order l and defect d is a partition of the positions [1, 4l] into 2l pairs
{a, a+p} in which each p in [d, d+l-1] is the difference of exactly two pairs.  In-bound: 3l >= 2d - 1.

This file builds one at EVERY in-bound cell (1 <= l <= L, 1 <= d <= floor((3l+1)/2)) from closed forms, and checks
each one with its own exact checker.  The chain:

  1. checker (check_mfold): the pairs partition [1, 2ml] and the difference multiset is exactly m x [d, d+l-1];
  2. l <= 4: the sixteen literal witnesses (found by a constraint solver, transcribed inline as data and
     re-checked here from the definition) -- the ONLY literal two-fold witnesses;
  3. splittable (l >= 5): least l1 with 3*l1 >= 2d-1 and 3(l-l1) >= 2(d+l1)-1, i.e. l1 = ceil((2d-1)/3) when
     5*l1 <= e = 3l-2d+1; build (d, l1) and (d+l1, l-l1) and concatenate (second shifted by 4*l1);
  4. unsplittable, l >= 5: signed-permutation route.  delta = d-l, mu = 2delta-1 (|mu| <= l is asserted).
     A permutation sigma of [1,l] with {|2(sigma(w)-w)+mu|} = {1,3,...,2l-1} is lifted by Lemma P + Lemma S.
       mu < 0 : solve (l, -mu), invert (Lemma INV);
       mu = 1 : reversal;  mu = l : tau_l;
       2mu <= l : l0 = mu + ((l-mu) mod mu); l0 = mu -> tau_mu; (l0,mu) = (4,3) -> l0 = 7 with [6,4,7,3,5,2,1];
                  else the band cell (l0, mu); then CINV applied (l-l0)/mu times (Lemma C composed with INV);
       band l/2 < mu < l : block-reversal families by l mod 4 (tables transcribed by hand below).
  5. assemble, check every cell, print route counts; then the m-fold tight line (m <= 6, odd l <= 41) from the
     paper's Table 1 (m copies).

Usage:  python verify_second.py L [--routes] [--log]     exit code 0 iff every cell with l <= L verified;
--routes writes routes_second_<L>.json and --log writes run_second_<L>.log beside this script.
No code is shared with verify.py; the family tables were transcribed independently from the note's class
tables (Appendix A), with the eight sporadic permutations as data.
"""
import sys, os, json, time

HERE = os.path.dirname(os.path.abspath(__file__))  # the folder of this script
KILL = os.path.join(HERE, "KILL")  # an optional stop file: create it to interrupt a long run
TIME_CAP = 2400.0  # seconds of wall time for one run (named cap; hitting it = UNKNOWN beyond the last full l)


class Killed(Exception):
    pass


def killed():
    return os.path.exists(KILL)


# ======================================================================================================
# 1. Checkers (exact integers)
# ======================================================================================================
def check_mfold(pairs, m, d, l):
    """True iff pairs partition [1, 2ml] and the differences are exactly m x [d, d+l-1]."""
    N = 2 * m * l
    if len(pairs) != m * l:
        return False, "pair count %d != %d" % (len(pairs), m * l)
    seen = bytearray(N + 1)
    cnt = [0] * l
    for pr in pairs:
        a, b = pr
        if type(a) is not int or type(b) is not int:
            return False, "non-integer entry"
        if not (1 <= a < b <= N):
            return False, "pair (%d,%d) out of range or unordered" % (a, b)
        if seen[a] or seen[b]:
            return False, "position repeated in (%d,%d)" % (a, b)
        seen[a] = 1
        seen[b] = 1
        p = b - a - d
        if p < 0 or p >= l:
            return False, "difference %d outside [d, d+l-1]" % (b - a)
        cnt[p] += 1
    # m*l pairs with 2ml distinct positions inside [1, 2ml]: a partition.
    for i, c in enumerate(cnt):
        if c != m:
            return False, "difference %d occurs %d times" % (d + i, c)
    return True, ""


def check_sigma(sig, l, mu):
    """Lemma P form: sigma a permutation of [1,l] with {|2(sigma(w)-w)+mu|} = {1,3,...,2l-1}."""
    if len(sig) != l:
        return False
    seen_v = bytearray(l + 1)
    seen_u = bytearray(l + 1)
    for w in range(1, l + 1):
        s = sig[w - 1]
        if type(s) is not int or not (1 <= s <= l) or seen_v[s]:
            return False
        seen_v[s] = 1
        x = 2 * (s - w) + mu
        if x % 2 == 0:
            return False
        u = (abs(x) + 1) // 2
        if not (1 <= u <= l) or seen_u[u]:
            return False
        seen_u[u] = 1
    return True


# ======================================================================================================
# 2. Literal witnesses, l <= 4 (found by a constraint solver), transcribed as data
# ======================================================================================================
LITERAL = {
    (1, 1): [[1, 2], [3, 4]],
    (2, 1): [[1, 3], [2, 4]],
    (1, 2): [[1, 2], [3, 5], [4, 6], [7, 8]],
    (2, 2): [[1, 3], [2, 5], [4, 7], [6, 8]],
    (3, 2): [[1, 4], [2, 6], [3, 7], [5, 8]],
    (1, 3): [[1, 2], [3, 4], [5, 7], [6, 9], [8, 11], [10, 12]],
    (2, 3): [[1, 4], [2, 6], [3, 7], [5, 8], [9, 11], [10, 12]],
    (3, 3): [[1, 4], [2, 6], [3, 8], [5, 10], [7, 11], [9, 12]],
    (4, 3): [[1, 5], [2, 7], [3, 9], [4, 10], [6, 11], [8, 12]],
    (5, 3): [[1, 8], [2, 7], [3, 9], [4, 10], [5, 12], [6, 11]],
    (1, 4): [[1, 4], [2, 3], [5, 7], [6, 10], [8, 11], [9, 13], [12, 14], [15, 16]],
    (2, 4): [[1, 3], [2, 7], [4, 8], [5, 9], [6, 11], [10, 13], [12, 15], [14, 16]],
    (3, 4): [[1, 5], [2, 6], [3, 8], [4, 9], [7, 13], [10, 16], [11, 14], [12, 15]],
    (4, 4): [[1, 5], [2, 7], [3, 9], [4, 11], [6, 13], [8, 14], [10, 15], [12, 16]],
    (5, 4): [[1, 6], [2, 8], [3, 10], [4, 12], [5, 13], [7, 14], [9, 15], [11, 16]],
    (6, 4): [[1, 7], [2, 11], [3, 10], [4, 12], [5, 13], [6, 15], [8, 14], [9, 16]],
}  # keys are (d, l)


# ======================================================================================================
# 3. Permutation tools: tau, reversal, inverse, shapes, CINV
# ======================================================================================================
def tau(n):
    """tau_n (n odd): reverse [1, (n+1)/2] and [(n+3)/2, n]."""
    m = (n - 1) // 2
    return [m + 2 - i for i in range(1, m + 2)] + [3 * m + 3 - i for i in range(m + 2, 2 * m + 2)]


def reversal(n):
    return [n + 1 - w for w in range(1, n + 1)]


def inverse(sig):
    inv = [0] * len(sig)
    for w, s in enumerate(sig, 1):
        inv[s - 1] = w
    return inv


def shape_sigma(sizes, order):
    """Sources [1,l] cut left to right into blocks of the given sizes; target intervals laid out left to right
    in `order` (a list of block indices); block i maps its source interval onto its target interval reversed."""
    b = len(sizes)
    a = [0] * b
    s = 0
    for i in range(b):
        a[i] = s
        s += sizes[i]
    l = s
    c = [0] * b
    s = 0
    for i in order:
        c[i] = s
        s += sizes[i]
    sig = [0] * l
    for i in range(b):
        n = sizes[i]
        for r in range(1, n + 1):
            sig[a[i] + r - 1] = c[i] + n + 1 - r
    return sig


def cinv_step(s0, n, mu):
    """Lemma C then INV: s0 solves (n, mu), 1 <= mu <= n; returns a solution of (n+mu, mu).
    sigma1(w) = s0(w) + mu (w <= n), sigma1(n+i) = tau_mu(i) (i <= mu) solves (n+mu, -mu); invert."""
    t = tau(mu)
    s1 = [x + mu for x in s0] + t
    return inverse(s1)


def cinv_power(s0, n, mu, k):
    """k CINV steps in closed form (cross-checked against cinv_step iteration).
    k = 2j: centre v in [j mu+1, j mu+n] -> s0(v - j mu) + j mu; for i' = 1..j the left block
    v in [(j-i')mu+1, (j-i'+1)mu] -> n + (i'+j-1)mu + tau(v - (j-i')mu) and the right block
    v in [n+(i'+j-1)mu+1, n+(i'+j)mu] -> (j-i')mu + tau(v - n - (i'+j-1)mu).  k odd: one more cinv_step."""
    if k == 0:
        return list(s0)
    j = k // 2
    t = tau(mu)
    N = n + 2 * j * mu
    s = [0] * N
    jm = j * mu
    for v in range(jm + 1, jm + n + 1):
        s[v - 1] = s0[v - jm - 1] + jm
    for ip in range(1, j + 1):
        lo = (j - ip) * mu
        base = n + (ip + j - 1) * mu
        for i in range(mu):
            s[lo + i] = base + t[i]
        lo2 = n + (ip + j - 1) * mu
        off = (j - ip) * mu
        for i in range(mu):
            s[lo2 + i] = off + t[i]
    if k % 2 == 1:
        s = cinv_step(s, N, mu)
    return s


def lemma_s(sig, l, mu):
    """Lemma P map + Lemma S (wedge-B): x_w = 2(sigma(w)-w)+mu, u = (|x|+1)/2, type S if x > 0 else D, pi(u) = w.
    S: (l+1-pi(u), 2l+u), (2l+1-u, 3l+pi(u));  D: (l+1-pi(u), 2l+1-u), (2l+u, 3l+pi(u)).
    Result: two-fold Langford sequence of order l, defect l + (mu+1)/2."""
    out = []
    ap = out.append
    for w in range(1, l + 1):
        x = 2 * (sig[w - 1] - w) + mu
        if x > 0:
            u = (x + 1) // 2
            ap((l + 1 - w, 2 * l + u))
            ap((2 * l + 1 - u, 3 * l + w))
        else:
            u = (1 - x) // 2
            ap((l + 1 - w, 2 * l + 1 - u))
            ap((2 * l + u, 3 * l + w))
    return out


SIGMA_7_3 = [6, 4, 7, 3, 5, 2, 1]  # the (7, 3) base replacing the impossible (4, 3)


# ======================================================================================================
# 4. Band families (transcribed by hand).  Each: sizes as (numerator, denominator) pairs in (l, mu),
#    the target order (block indices, target intervals left to right), congruence and domain.
# ======================================================================================================
FAMILIES = {}
BAND_ORDER = {0: [], 1: [], 2: [], 3: []}


def fam(name, src, lres, order, cong, dom, sizes):
    FAMILIES[name] = dict(name=name, src=src, lres=lres, order=tuple(order), cong=cong, dom=dom, sizes=sizes)
    BAND_ORDER[lres].append(name)


def eval_sizes(f, l, mu):
    """Returns the size list if every size is an integer >= 1, else None."""
    out = []
    for num, den in f['sizes'](l, mu):
        if num % den != 0:
            return None
        v = num // den
        if v < 1:
            return None
        out.append(v)
    return out


# ---- l = 2 (mod 4): FA, FB2, FB6, F4 (the note's Appendix A); h = (mu+1)/2 ----
def _q2(l):
    return (l - 2) // 4


fam("FA", "Appendix A", 2, (2, 3, 0, 4, 1),
    lambda l, mu: l % 4 == 2,
    lambda l, mu: _q2(l) + 2 <= (mu + 1) // 2 and 2 * ((mu + 1) // 2) <= 3 * _q2(l) + 2,
    lambda l, mu: [((mu + 1) // 2 - 1, 1), (_q2(l) + 1, 1), (3 * _q2(l) + 3 - 2 * ((mu + 1) // 2), 1),
                   (_q2(l), 1), ((mu + 1) // 2 - _q2(l) - 1, 1)])
fam("FB2", "Appendix A", 2, (1, 3, 0, 4, 2),
    lambda l, mu: l % 8 == 2,
    lambda l, mu: (l - 2) // 8 >= 1 and 3 * ((l - 2) // 8) + 2 <= (mu + 1) // 2 <= 4 * ((l - 2) // 8) + 1,
    lambda l, mu: [((mu + 1) // 2 - (l - 2) // 8 - 1, 1), ((l - 2) // 8, 1), (3 * ((l - 2) // 8) + 1, 1),
                   (8 * ((l - 2) // 8) + 3 - 2 * ((mu + 1) // 2), 1), ((mu + 1) // 2 - 3 * ((l - 2) // 8) - 1, 1)])
fam("FB6", "Appendix A", 2, (1, 3, 0, 4, 2),
    lambda l, mu: l % 8 == 6,
    lambda l, mu: 3 * ((l - 6) // 8) + 4 <= (mu + 1) // 2 <= 4 * ((l - 6) // 8) + 3,
    lambda l, mu: [((mu + 1) // 2 - (l - 6) // 8 - 1, 1), ((l - 6) // 8 + 1, 1), (3 * ((l - 6) // 8) + 2, 1),
                   (8 * ((l - 6) // 8) + 7 - 2 * ((mu + 1) // 2), 1), ((mu + 1) // 2 - 3 * ((l - 6) // 8) - 3, 1)])
fam("F4", "Appendix A", 2, (2, 0, 3, 1),
    lambda l, mu: l % 8 == 6,
    lambda l, mu: mu == 6 * ((l - 6) // 8) + 5,
    lambda l, mu: [(3 * ((l - 6) // 8) + 2, 1), (2 * ((l - 6) // 8) + 2, 1), (2 * ((l - 6) // 8) + 1, 1),
                   ((l - 6) // 8 + 1, 1)])


# ---- l = 0 (mod 4): A1, A3, U1, U3, U5, U7, V, T (the note's Appendix A: sizes, orders, full domains) ----
def _all_nonneg(*vals):
    return all(v >= 0 for v in vals)


fam("A1", "Appendix A", 0, (8, 3, 6, 7, 2, 0, 5, 1, 4),
    lambda l, mu: l % 4 == 0 and mu % 4 == 1,
    lambda l, mu: _all_nonneg(-l + 2 * mu - 2, -l + 2 * mu + 2, mu - 5, l - mu - 3, l - mu - 1, l - 8, l - 2, l - 1,
                              2 * l - mu - 3, 2 * l - mu - 1, 2 * l - mu + 1, 3 * l - 4 * mu - 8),
    lambda l, mu: [(mu - 1, 4), (1, 1), (l - mu + 1, 4), (2 * mu - l + 2, 4), (mu - 1, 4), (mu - 1, 4),
                   (3 * l - 4 * mu - 4, 4), (l - 4, 4), (1, 1)])
fam("A3", "Appendix A", 0, (8, 3, 6, 7, 2, 0, 5, 1, 4),
    lambda l, mu: l % 4 == 0 and mu % 4 == 3,
    lambda l, mu: _all_nonneg(-l + 2 * mu - 2, -l + 2 * mu + 2, mu - 7, mu - 3, l - mu - 5, l - mu - 1, l - 8, l - 2,
                              l - 1, 2 * l - mu - 3, 2 * l - mu - 1, 2 * l - mu + 1, 3 * l - 4 * mu - 8),
    lambda l, mu: [(mu + 1, 4), (1, 1), (l - mu - 1, 4), (2 * mu - l + 2, 4), (mu - 3, 4), (mu + 1, 4),
                   (3 * l - 4 * mu - 4, 4), (l - 4, 4), (1, 1)])
fam("U1", "Appendix A", 0, (5, 7, 1, 3, 4, 0, 2, 6),
    lambda l, mu: l % 4 == 0 and mu % 8 == 1,
    lambda l, mu: _all_nonneg(-2 * l + 3 * mu - 11, mu - 5, mu - 1, mu + 1, l - mu - 3, 2 * l - mu - 15, 2 * l - mu - 7,
                              2 * l - mu - 3, 2 * l - mu - 1, 2 * l - mu + 1, 2 * l - mu + 5, 2 * l + mu - 1),
    lambda l, mu: [(2 * l - mu + 1, 8), (3 * mu - 2 * l - 3, 8), (mu + 3, 4), (2 * l - mu + 1, 8),
                   (2 * l - mu - 7, 8), (1, 1), (mu - 1, 4), (l - mu - 1, 2)])
fam("U3", "Appendix A", 0, (5, 8, 0, 3, 6, 4, 1, 7, 2),
    lambda l, mu: l % 4 == 0 and mu % 8 == 3,
    lambda l, mu: _all_nonneg(-2 * l + 3 * mu - 1, mu - 7, mu - 3, mu + 1, l - mu - 3, 2 * l - mu - 29, 2 * l - mu - 13,
                              2 * l - mu - 9, 2 * l - mu - 5, 2 * l - mu - 1, 2 * l - mu + 7, 2 * l + mu + 1),
    lambda l, mu: [(mu - 3, 4), (mu + 1, 4), (2 * l - mu + 3, 8), (2 * l - mu - 21, 8), (1, 1), (1, 1),
                   (2 * l - mu + 3, 8), (3 * mu - 2 * l + 7, 8), (l - mu - 1, 2)])
fam("U5", "Appendix A", 0, (4, 7, 0, 3, 5, 1, 6, 2),
    lambda l, mu: l % 4 == 0 and mu % 8 == 5,
    lambda l, mu: _all_nonneg(-2 * l + 3 * mu - 7, mu - 5, mu - 1, mu + 1, l - mu - 3, 2 * l - mu - 11, 2 * l - mu - 3,
                              2 * l - mu - 1, 2 * l - mu + 1, 2 * l - mu + 5, 2 * l + mu + 3),
    lambda l, mu: [(mu - 1, 4), (mu + 3, 4), (2 * l - mu - 3, 8), (2 * l - mu - 3, 8), (1, 1), (2 * l - mu - 3, 8),
                   (3 * mu - 2 * l + 1, 8), (l - mu - 1, 2)])
fam("U7", "Appendix A", 0, (1, 6, 2, 4, 7, 0, 8, 3, 5),
    lambda l, mu: l % 4 == 0 and mu % 8 == 7,
    lambda l, mu: _all_nonneg(-4 * l + 5 * mu - 11, -4 * l + 5 * mu + 1, mu - 7, mu + 1, l - mu - 1, l - mu + 1,
                              2 * l - mu - 5, 2 * l - mu + 1, 4 * l - 3 * mu + 1, 4 * l - mu + 3),
    lambda l, mu: [(mu + 1, 8), (mu + 1, 8), (mu + 1, 8), (2 * l - mu - 1, 4), (5 * mu - 4 * l - 3, 8), (mu + 1, 8),
                   (l - mu, 1), (l - mu + 1, 2), (5 * mu - 4 * l - 3, 8)])
fam("V", "Appendix A", 0, (8, 0, 5, 7, 3, 4, 1, 2, 6),
    lambda l, mu: l % 4 == 0 and mu % 4 == 3,
    lambda l, mu: _all_nonneg(-3 * l + 5 * mu - 11, -2 * l + 3 * mu - 9, -2 * l + 3 * mu - 7, -2 * l + 3 * mu - 3,
                              -l + 2 * mu - 6, -l + 2 * mu - 2, mu - 7, mu - 3, mu - 1, l - mu - 5, l - mu - 1,
                              l - mu + 2, l + 2, 2 * l - mu + 1, 2 * l - mu + 3, 3 * l - 3 * mu + 5, 4 * l - 5 * mu + 3),
    lambda l, mu: [(l - mu + 3, 4), (mu - 3, 4), (mu + 1, 4), (4 * l - 5 * mu + 7, 4), (3 * mu - 2 * l - 5, 4),
                   (5 * mu - 3 * l - 7, 4), (2 * mu - l - 2, 4), (4 * l - 5 * mu + 7, 4), (l - mu - 1, 4)])
fam("T", "Appendix A", 0, (2, 3, 6, 0, 4, 1, 5),
    lambda l, mu: l % 4 == 0 and mu % 8 == 3,
    lambda l, mu: _all_nonneg(-8 * l + 9 * mu - 11, -4 * l + 5 * mu + 1, mu - 11, mu - 3, l - mu - 1, l - mu + 1,
                              2 * l - mu + 1, 4 * l - 3 * mu - 3, 4 * l - 3 * mu + 1, 4 * l - 3 * mu + 5,
                              4 * l - mu + 3, 8 * l - 7 * mu - 3),
    lambda l, mu: [(mu + 1, 4), (mu - 3, 8), (8 * l - 7 * mu + 5, 8), (9 * mu - 8 * l - 3, 8), (mu - 3, 8),
                   (mu + 1, 4), (l - mu, 1)])

# the eight sporadic cells (l, mu) -> sigma (the note prints them)
SPORADIC_R0 = {
    (8, 5): [2, 6, 8, 7, 5, 4, 3, 1],
    (8, 7): [1, 5, 4, 8, 7, 2, 6, 3],
    (12, 9): [7, 6, 5, 1, 12, 11, 10, 4, 9, 8, 3, 2],
    (12, 11): [2, 1, 3, 9, 8, 12, 11, 10, 7, 6, 5, 4],
    (16, 11): [1, 4, 12, 11, 10, 16, 15, 14, 13, 9, 8, 7, 6, 5, 3, 2],
    (20, 15): [2, 1, 14, 13, 12, 11, 10, 20, 19, 18, 17, 16, 15, 7, 6, 5, 4, 3, 9, 8],
    (24, 17): [2, 1, 17, 16, 15, 14, 13, 12, 24, 23, 22, 21, 20, 19, 18, 9, 8, 7, 6, 5, 4, 3, 11, 10],
    (32, 23): [2, 1, 23, 22, 21, 20, 19, 18, 17, 16, 15, 3, 32, 31, 30, 29, 28, 27, 26, 25, 24, 11, 10, 9, 8, 7, 6,
               5, 4, 14, 13, 12],
}

# ---- l = 1 (mod 4): TT, FT, FA1, FA3, FL1, FL5 (the note's Appendix A) ----
fam("TT1", "Appendix A", 1, (0, 1),
    lambda l, mu: l % 4 == 1,
    lambda l, mu: mu == l and l >= 5,
    lambda l, mu: [(l + 1, 2), (l - 1, 2)])
fam("FT", "Appendix A", 1, (5, 1, 3, 0, 4, 2),
    lambda l, mu: l % 4 == 1,
    lambda l, mu: mu == l - 2 and l >= 9,
    lambda l, mu: [(l - 1, 4), (l - 5, 4), (l - 1, 4), (1, 1), (l - 1, 4), (1, 1)])
fam("FA1", "Appendix A", 1, (7, 1, 3, 4, 0, 5, 2, 6),
    lambda l, mu: l % 4 == 1 and mu % 4 == 1,
    lambda l, mu: 2 * mu >= l + 5 and mu <= l - 4,
    lambda l, mu: [(mu - 1, 4), (mu - 5, 4), (l - 1, 4), (l - mu, 4), (l - mu + 4, 4), (2 * mu - l - 1, 4), (1, 1),
                   (l - mu, 2)])
fam("FA3", "Appendix A", 1, (6, 1, 3, 4, 0, 5, 2),
    lambda l, mu: l % 4 == 1 and mu % 4 == 3,
    lambda l, mu: 2 * mu >= l + 5 and mu <= l - 6,
    lambda l, mu: [(mu + 1, 4), (mu + 1, 4), (l - 1, 4), (l - mu - 2, 4), (l - mu + 2, 4), (2 * mu - l - 1, 4),
                   (l - mu, 2)])
fam("FL1", "Appendix A", 1, (6, 0, 2, 4, 5, 1, 3),
    lambda l, mu: l % 8 == 1,
    lambda l, mu: 2 * mu == l + 1 and l >= 17,
    lambda l, mu: [(1, 1), (l - 1, 8), (l - 9, 8), (l - 1, 4), (l - 1, 8), (l + 7, 8), (l - 1, 4)])
fam("FL5", "Appendix A", 1, (5, 1, 3, 4, 0, 2),
    lambda l, mu: l % 8 == 5,
    lambda l, mu: 2 * mu == l + 1 and l >= 13,
    lambda l, mu: [(l + 3, 8), (l + 3, 8), (l - 1, 4), (l - 5, 8), (l + 3, 8), (l - 1, 4)])

BASE_R1 = {(5, 3): [3, 5, 2, 4, 1], (9, 5): [6, 5, 9, 8, 1, 7, 4, 3, 2]}  # the two explicit bases


# ---- l = 3 (mod 4): TT, R3T1, R3O, R3E, R3Q (the note's Appendix A), l = 4q+3, t = (l-mu)/2 ----
def _qt(l, mu):
    return (l - 3) // 4, (l - mu) // 2


fam("TT3", "Appendix A", 3, (0, 1),
    lambda l, mu: l % 4 == 3,
    lambda l, mu: mu == l,
    lambda l, mu: [(l + 1, 2), (l - 1, 2)])
fam("R3T1", "Appendix A", 3, (5, 1, 3, 0, 4, 2),
    lambda l, mu: l % 4 == 3,
    lambda l, mu: _qt(l, mu)[1] == 1 and _qt(l, mu)[0] >= 1,
    lambda l, mu: [(_qt(l, mu)[0], 1), (_qt(l, mu)[0], 1), (_qt(l, mu)[0] + 1, 1), (1, 1), (_qt(l, mu)[0], 1),
                   (1, 1)])
fam("R3O", "Appendix A", 3, (6, 1, 3, 4, 0, 5, 2),
    lambda l, mu: l % 4 == 3 and ((l - mu) // 2) % 2 == 1,
    lambda l, mu: 3 <= _qt(l, mu)[1] <= _qt(l, mu)[0],
    lambda l, mu: (lambda q, t: [(2 * q + 1 - t, 2), (2 * q + 1 - t, 2), (q + 1, 1), (t - 1, 2), (t + 1, 2),
                                 (q + 1 - t, 1), (t, 1)])(*_qt(l, mu)))
fam("R3E", "Appendix A", 3, (7, 0, 2, 4, 5, 1, 6, 3),
    lambda l, mu: l % 4 == 3 and ((l - mu) // 2) % 2 == 0,
    lambda l, mu: 2 <= _qt(l, mu)[1] <= _qt(l, mu)[0] - 1,
    lambda l, mu: (lambda q, t: [(1, 1), (2 * q + 2 - t, 2), (2 * q - t, 2), (q, 1), (t, 2), (t + 2, 2),
                                 (q - t, 1), (t, 1)])(*_qt(l, mu)))
fam("R3Q", "Appendix A", 3, (6, 0, 2, 4, 5, 1, 3),
    lambda l, mu: l % 4 == 3 and ((l - mu) // 2) % 2 == 0,
    lambda l, mu: 2 * _qt(l, mu)[0] + 2 <= 3 * _qt(l, mu)[1] and _qt(l, mu)[1] <= _qt(l, mu)[0],
    lambda l, mu: (lambda q, t: [(2 * q + 1 - 2 * t, 1), (2 * q + 2 - t, 2), (3 * t - 2 * q, 2), (t, 1),
                                 (2 * q - t, 2), (2 * q + 2 - t, 2), (t, 1)])(*_qt(l, mu)))

ANOMALIES = []  # (family, l, mu, what): a domain that holds where the sizes are invalid, or a failed sigma


def try_family(name, l, mu):
    f = FAMILIES[name]
    if not f['cong'](l, mu) or not f['dom'](l, mu):
        return None
    sz = eval_sizes(f, l, mu)
    if sz is None:
        ANOMALIES.append((name, l, mu, "domain holds but sizes not integers >= 1"))
        return None
    if sum(sz) != l:
        ANOMALIES.append((name, l, mu, "sizes do not sum to l"))
        return None
    return shape_sigma(sz, f['order'])


def band_sigma(l, mu):
    """l >= 5, l/2 < mu <= l, mu odd.  Returns (sigma, family name)."""
    r = l % 4
    for name in BAND_ORDER[r]:
        sig = try_family(name, l, mu)
        if sig is not None:
            return sig, name
    if r == 0 and (l, mu) in SPORADIC_R0:
        return list(SPORADIC_R0[(l, mu)]), "SPORADIC_R0"
    if r == 1 and (l, mu) in BASE_R1:
        return list(BASE_R1[(l, mu)]), "BASE_R1"
    raise RuntimeError("band cell (l=%d, mu=%d) not covered by any transcribed family" % (l, mu))


def sp_sigma_pos(l, mu):
    """0 < mu <= l, mu odd, l >= 1.  Returns (sigma, route)."""
    if mu == 1:
        return reversal(l), "REV(mu=1)"
    if mu == l:
        return tau(l), "TAU(mu=l)"
    if 2 * mu <= l:
        l0 = mu + (l - mu) % mu
        if l0 == mu:
            base, bname = tau(mu), "TAU(divisor)"
        elif (l0, mu) == (4, 3):
            l0 = 7
            base, bname = list(SIGMA_7_3), "BASE(7,3)"
        else:
            base, bname = band_sigma(l0, mu)
        k = (l - l0) // mu
        if k == 0:
            return base, bname
        return cinv_power(base, l0, mu, k), "CINV<-" + bname
    return band_sigma(l, mu)


def sp_sigma(l, mu):
    if mu < 0:
        s, r = sp_sigma_pos(l, -mu)
        return inverse(s), "INV." + r
    return sp_sigma_pos(l, mu)


# ======================================================================================================
# 5. Assembly of one cell (recursive concatenation with offsets)
# ======================================================================================================
class Stats:
    def __init__(self):
        self.literal_used = set()
        self.leaf = {}
        self.sp_fail = []

    def add_leaf(self, k):
        self.leaf[k] = self.leaf.get(k, 0) + 1


def build(d, l, off, out, st):
    """Appends the pairs of a two-fold sequence (d, l), shifted by off, to out.  Returns the top-level route."""
    if l <= 4:
        for a, b in LITERAL[(d, l)]:
            out.append((a + off, b + off))
        st.literal_used.add((d, l))
        st.add_leaf("literal")
        return "literal"
    l1 = (2 * d + 1) // 3  # = ceil((2d-1)/3), the least l1 with 3 l1 >= 2d-1 (and l1 >= 1)
    if 5 * l1 <= 3 * l - 2 * d + 1:
        build(d, l1, off, out, st)
        build(d + l1, l - l1, off + 4 * l1, out, st)
        return "concat(l1=%d)" % l1
    mu = 2 * (d - l) - 1
    if not (-l <= mu <= l):
        raise RuntimeError("unsplittable cell (d=%d, l=%d) with |mu| = %d > l" % (d, l, abs(mu)))
    sig, route = sp_sigma(l, mu)
    if not check_sigma(sig, l, mu):
        st.sp_fail.append((d, l, mu, route))
        raise RuntimeError("sigma check failed at (d=%d, l=%d, mu=%d) via %s" % (d, l, mu, route))
    for a, b in lemma_s(sig, l, mu):
        out.append((a + off, b + off))
    st.add_leaf("SP:" + route)
    return "SP:" + route


def route_class(route):
    """Aggregate label: literal / concatenation / SP-band:<fam> / SP-CINV:<base> / SP-REV / SP-TAU..."""
    if route == "literal":
        return "literal"
    if route.startswith("concat"):
        return "concatenation"
    r = route[3:]
    if r.startswith("INV."):
        r = r[4:]
    if r.startswith("CINV<-"):
        return "SP CINV chain (base " + r[6:] + ")"
    if r.startswith("REV") or r.startswith("TAU"):
        return "SP " + r
    if r.startswith("BASE(7,3)"):
        return "SP base (7,3)"
    return "SP band family " + r


# ======================================================================================================
# 6. Sections
# ======================================================================================================
class Log:
    """Prints every line; with a path (--log) it also appends the line to that file."""

    def __init__(self, path):
        self.f = open(path, "w", encoding="utf-8") if path else None

    def __call__(self, *a):
        s = " ".join(str(x) for x in a)
        print(s, flush=True)
        if self.f:
            self.f.write(s + "\n")
            self.f.flush()

    def close(self):
        if self.f:
            self.f.close()


def sec_literals(log):
    ok_all = True
    for (d, l), pairs in sorted(LITERAL.items(), key=lambda kv: (kv[0][1], kv[0][0])):
        ok, why = check_mfold([tuple(p) for p in pairs], 2, d, l)
        if not ok:
            ok_all = False
            log("  LITERAL FAIL (d=%d, l=%d): %s" % (d, l, why))
    cells = [(d, l) for l in range(1, 5) for d in range(1, (3 * l + 1) // 2 + 1)]
    missing = [c for c in cells if c not in LITERAL]
    log("  16 literal witnesses (l <= 4) re-checked: %s; in-bound cells with l <= 4: %d, missing: %s"
        % ("all pass" if ok_all else "FAILURES", len(cells), missing))
    return ok_all and not missing


def sec_negative_control(log):
    """Mutated witnesses must be rejected."""
    rejected = 0
    total = 0
    for (d, l) in [(3, 4), (6, 4), (5, 3)]:
        base = [tuple(p) for p in LITERAL[(d, l)]]
        muts = []
        a, b = base[0]
        muts.append([(a, b + 1)] + base[1:])                 # difference changed
        muts.append(base[:-1])                               # a pair dropped
        muts.append([(b, a)] + base[1:])                     # unordered pair
        c, e = base[1]
        muts.append([(a, e), (c, b)] + base[2:])             # endpoints swapped
        muts.append(base + [(4 * l + 1, 4 * l + 1 + d)])     # extra pair
        for mm in muts:
            total += 1
            ok, _ = check_mfold(mm, 2, d, l)
            if not ok:
                rejected += 1
    ok, _ = check_mfold([tuple(p) for p in LITERAL[(3, 4)]], 2, 4, 4)  # right pairs, wrong d
    total += 1
    rejected += (not ok)
    good = [1, 2, 3, 4, 5]
    bad = [1, 2, 3, 5, 4]
    s_ok = check_sigma(tau(5), 5, 5) and not check_sigma(bad, 5, 5) and not check_sigma(good, 5, 5)
    log("  negative control: %d of %d mutated two-fold witnesses rejected; sigma checker control: %s"
        % (rejected, total, "ok" if s_ok else "FAIL"))
    return rejected == total and s_ok


def sec_domain_scan(log, lscan):
    """For each family: every cell with l <= lscan, 1 <= mu <= l (mu odd) in its congruence class with integral
    sizes >= 1 is built and sigma-checked; the domain must hold only where the check passes."""
    bad_total = 0
    for name, f in FAMILIES.items():
        n_in_ok = n_in_bad = n_in_invalid = n_out_ok = n_out_bad = 0
        firstbad = None
        for l in range(1, lscan + 1):
            if killed():
                raise Killed()
            if l % 4 != f['lres']:
                continue
            for mu in range(1, l + 1, 2):
                if not f['cong'](l, mu):
                    continue
                indom = f['dom'](l, mu)
                sz = eval_sizes(f, l, mu)
                if sz is None or sum(sz) != l:
                    if indom:
                        n_in_invalid += 1
                        firstbad = firstbad or (l, mu, "invalid sizes")
                    continue
                ok = check_sigma(shape_sigma(sz, f['order']), l, mu)
                if indom and ok:
                    n_in_ok += 1
                elif indom:
                    n_in_bad += 1
                    firstbad = firstbad or (l, mu, "sigma fails")
                elif ok:
                    n_out_ok += 1
                else:
                    n_out_bad += 1
        bad = n_in_bad + n_in_invalid
        bad_total += bad
        log("  %-5s %-22s order %-28s in-domain pass %5d | in-domain FAIL %d | outside-domain, sizes ok: pass %d, fail %d%s"
            % (name, f['src'], "".join(str(x) for x in f['order']), n_in_ok, bad, n_out_ok, n_out_bad,
               ("  first bad %s" % (firstbad,)) if firstbad else ""))
    for tbl, nm in ((SPORADIC_R0, "SPORADIC_R0"), (BASE_R1, "BASE_R1")):
        good = sum(1 for (l, mu), s in tbl.items() if check_sigma(s, l, mu))
        log("  %s: %d of %d explicit sigmas pass" % (nm, good, len(tbl)))
        bad_total += len(tbl) - good
    ok73 = check_sigma(SIGMA_7_3, 7, 3)
    log("  BASE(7,3) sigma [6,4,7,3,5,2,1]: %s" % ("pass" if ok73 else "FAIL"))
    return bad_total == 0 and ok73


def sec_cinv_crosscheck(log, lmax):
    """Closed-form cinv_power against iterated cinv_step, on every chain (l, mu) with 3 <= mu, 2mu <= l <= lmax."""
    n = 0
    bad = 0
    for l in range(6, lmax + 1):
        if killed():
            raise Killed()
        for mu in range(3, l // 2 + 1, 2):
            l0 = mu + (l - mu) % mu
            if l0 == mu:
                base = tau(mu)
            elif (l0, mu) == (4, 3):
                l0, base = 7, list(SIGMA_7_3)
            else:
                base = band_sigma(l0, mu)[0]
            k = (l - l0) // mu
            s_it = list(base)
            nn = l0
            for _ in range(k):
                s_it = cinv_step(s_it, nn, mu)
                nn += mu
            s_cf = cinv_power(base, l0, mu, k)
            n += 1
            if s_it != s_cf or not check_sigma(s_cf, l, mu):
                bad += 1
    log("  CINV closed form vs iterated Lemma C + INV: %d chains (l <= %d), %d mismatches" % (n, lmax, bad))
    return bad == 0


def sec_band_census(log, lmax):
    """Every band cell 5 <= l <= lmax, l/2 < mu <= l (mu odd): first family in the fixed order; sigma check."""
    counts = {r: {} for r in range(4)}
    rng = {r: {} for r in range(4)}
    bad = 0
    for l in range(5, lmax + 1):
        if killed():
            raise Killed()
        for mu in range(l // 2 + 1, l + 1):
            if mu % 2 == 0 or 2 * mu <= l:
                continue
            try:
                sig, name = band_sigma(l, mu)
            except RuntimeError as ex:
                log("  UNCOVERED band cell (l=%d, mu=%d): %s" % (l, mu, ex))
                bad += 1
                continue
            if not check_sigma(sig, l, mu):
                log("  BAND SIGMA FAIL (l=%d, mu=%d) via %s" % (l, mu, name))
                bad += 1
            c = counts[l % 4]
            c[name] = c.get(name, 0) + 1
            if l <= 400:
                rr = rng[l % 4]
                rr[name] = rr.get(name, 0) + 1
    for r in (0, 1, 2, 3):
        tot = sum(counts[r].values())
        log("  l = %d (mod 4), 5 <= l <= %d: %d band cells; %s" % (r, lmax, tot,
                                                                  ", ".join("%s %d" % kv for kv in counts[r].items())))
        if lmax > 400:
            log("      (of which l <= 400: %s)" % ", ".join("%s %d" % kv for kv in rng[r].items()))
    return bad == 0


def mfold_tight(m, l):
    """m copies of the paper's Table 1 (Construction 2.1, Langford L_{2d0-1}^{d0}, d0 = (l+1)/2):
    rows i = d0+2r: (d0-r, 2d0+r), 0 <= r <= d0-1;  i = d0+2r+1: (2d0-1-r, 3d0+r), 0 <= r <= d0-2.
    Copy k: (a + k l, b + (m-1) l + k l).  Defect ((2m-1) l + 1)/2."""
    d0 = (l + 1) // 2
    base = [(d0 - r, 2 * d0 + r) for r in range(d0)] + [(2 * d0 - 1 - r, 3 * d0 + r) for r in range(d0 - 1)]
    pairs = []
    for k in range(m):
        for a, b in base:
            pairs.append((a + k * l, b + (m - 1) * l + k * l))
    return ((2 * m - 1) * l + 1) // 2, pairs


def sec_mfold(log):
    n = 0
    bad = 0
    for m in range(1, 7):
        for l in range(1, 42, 2):
            d, pairs = mfold_tight(m, l)
            ok, why = check_mfold(pairs, m, d, l)
            n += 1
            if not ok:
                bad += 1
                log("  m-fold tight FAIL m=%d l=%d d=%d: %s" % (m, l, d, why))
            if (2 * m - 1) * l != 2 * d - 1:
                bad += 1
                log("  m-fold tight cell not on the counting line: m=%d l=%d d=%d" % (m, l, d))
    log("  m-fold tight line, m = 1..6, odd l = 1..41: %d cells, %d failures (each on the line (2m-1)l = 2d-1)"
        % (n, bad))
    return bad == 0


def sec_main(log, L, write_routes, t0):
    st = Stats()
    route_counts = {}
    class_counts = {}
    inv_count = 0
    routes = []
    ncell = 0
    nfail = 0
    last_full = 0
    max_bad_mu = 0
    for l in range(1, L + 1):
        if killed():
            log("  KILL file seen at l = %d; stopping" % l)
            raise Killed()
        if time.time() - t0 > TIME_CAP:
            log("  TIME CAP %.0f s hit at l = %d; cells with l >= %d are UNKNOWN for this run" % (TIME_CAP, l, l))
            return False, last_full, st, route_counts, class_counts, inv_count, ncell, nfail
        lfail = 0
        for d in range(1, (3 * l + 1) // 2 + 1):
            out = []
            try:
                route = build(d, l, 0, out, st)
            except RuntimeError as ex:
                log("  BUILD FAIL (d=%d, l=%d): %s" % (d, l, ex))
                nfail += 1
                lfail += 1
                continue
            ok, why = check_mfold(out, 2, d, l)
            ncell += 1
            if not ok:
                log("  CHECK FAIL (d=%d, l=%d) via %s: %s" % (d, l, route, why))
                nfail += 1
                lfail += 1
                continue
            key = route if not route.startswith("concat") else "concat"
            route_counts[key] = route_counts.get(key, 0) + 1
            cc = route_class(route)
            class_counts[cc] = class_counts.get(cc, 0) + 1
            if ".INV." in route or route.startswith("SP:INV."):
                inv_count += 1
            if write_routes:
                routes.append([l, d, route])
        if lfail == 0 and last_full == l - 1:
            last_full = l
        if l % 50 == 0:
            log("  ... l = %d done (%d cells so far, %d failures, %.1f s)" % (l, ncell, nfail, time.time() - t0))
    if write_routes:
        path = os.path.join(HERE, "routes_second_%d.json" % L)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write('{"script": "verify_second.py", "L": %d, "format": "[l, d, top-level route]", "cells": [\n' % L)
            fh.write(",\n".join(json.dumps(r) for r in routes))
            fh.write("\n]}\n")
        log("  per-cell routes written to routes_second_%d.json (%d cells)" % (L, len(routes)))
    return nfail == 0, last_full, st, route_counts, class_counts, inv_count, ncell, nfail


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    L = int(args[0]) if args else 300
    write_routes = "--routes" in sys.argv
    log = Log(os.path.join(HERE, "run_second_%d.log" % L) if "--log" in sys.argv else None)
    t0 = time.time()
    log("verify_second.py -- L = %d, started %s" % (L, time.strftime("%Y-%m-%d %H:%M:%S")))
    log("python %s; stdlib only; an optional file KILL beside this script stops a run" % sys.version.split()[0])
    results = {}
    try:
        log("[1] literal witnesses (l <= 4)")
        results["literals"] = sec_literals(log)
        log("[2] checker negative control")
        results["negctl"] = sec_negative_control(log)
        log("[3] family transcription scan (every family, l <= 160, all odd 1 <= mu <= l in its class)")
        results["domscan"] = sec_domain_scan(log, 160)
        log("[4] CINV closed form cross-check")
        results["cinv"] = sec_cinv_crosscheck(log, 150)
        lband = max(L, 400)
        log("[5] band census (every band cell, 5 <= l <= %d; fixed family order per class)" % lband)
        for r in range(4):
            log("      order l = %d (mod 4): %s%s" % (r, ", ".join(BAND_ORDER[r]),
                                                  {0: ", SPORADIC_R0", 1: ", BASE_R1", 2: "", 3: ""}[r]))
        results["band"] = sec_band_census(log, lband)
        log("[6] main sweep: every in-bound cell 1 <= l <= %d, 1 <= d <= floor((3l+1)/2)" % L)
        ok, last_full, st, rc, cc, invc, ncell, nfail = sec_main(log, L, write_routes, t0)
        results["main"] = ok
        log("  cells built and checked: %d; failures: %d; every cell with l <= %d verified" % (ncell, nfail, last_full))
        log("  top-level routes by class:")
        for k in sorted(cc, key=lambda k: (-cc[k], k)):
            log("    %-45s %7d" % (k, cc[k]))
        log("  of the SP cells, %d go through Lemma INV (mu < 0)" % invc)
        merged = {}
        for k, v in rc.items():
            base = k.replace("SP:INV.", "SP:")
            dv = merged.setdefault(base, [0, 0])
            dv[1 if k.startswith("SP:INV.") else 0] += v
        log("  top-level routes, exact labels (direct mu > 0 / through INV mu < 0):")
        for k in sorted(merged, key=lambda k: (-sum(merged[k]), k)):
            log("    %-40s %7d / %7d" % (k, merged[k][0], merged[k][1]))
        leafc = {}
        for k, v in st.leaf.items():
            c = route_class(k)
            leafc[c] = leafc.get(c, 0) + v
        log("  leaf uses by class (every block placed over all cells, concatenation pieces included):")
        for k in sorted(leafc, key=lambda k: (-leafc[k], k)):
            log("    %-45s %9d" % (k, leafc[k]))
        log("  literal witnesses used: %d distinct: %s" % (len(st.literal_used),
                                                        sorted(st.literal_used, key=lambda c: (c[1], c[0]))))
        log("[7] m-fold tight line (paper Table 1, m copies)")
        results["mfold"] = sec_mfold(log)
        if ANOMALIES:
            log("  ANOMALIES (domain holds, sizes invalid): %d, first %s" % (len(ANOMALIES), ANOMALIES[:5]))
        allok = all(results.values()) and not ANOMALIES and last_full == L
        log("VERDICT: %s -- every in-bound two-fold cell with l <= %d built from closed forms (plus 16 literal "
            "witnesses at l <= 4) and verified by the exact checker: %s; sections %s; %.1f s"
            % ("PASS" if allok else "FAIL", L, "yes" if last_full == L and results["main"] else "NO",
               results, time.time() - t0))
        log.close()
        return 0 if allok else 1
    except Killed:
        log("KILLED: stopped on the KILL file; verdict UNKNOWN")
        log.close()
        return 2


if __name__ == "__main__":
    sys.exit(main())
