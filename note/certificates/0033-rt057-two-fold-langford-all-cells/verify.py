#!/usr/bin/env python3
"""verify.py -- a two-fold Langford sequence at every in-bound cell, from the closed forms.

A two-fold Langford sequence at EVERY in-bound cell (1 <= l <= L, 1 <= d <= floor((3l+1)/2)),
built from closed forms (plus the census literals at l <= 4 and a tiny exact search for the
eight band-r0 sporadic cells), each one checked by the exact checker below.

Standalone, stdlib only.  Usage:  python twofold_all.py L   (exit 0 iff every cell verified).

Definitions: a two-fold Langford sequence of order l and defect d
is a partition of [1, 4l] into 2l pairs {a, a+p} in which each p in [d, d+l-1] is the
difference of exactly two pairs.  m-fold: [1, 2ml], m*l pairs, each difference m times.

Chain:
  1. checker (check_mfold);
  2. literal census witnesses (all 16 cells l <= 4 re-checked), used only at unsplittable cells
     with l <= 4 where no closed form applies -- (d, l) = (3, 4), (6, 4) -- or at every
     unsplittable l <= 4 cell with --census-small;
  3. concatenation at splittable cells (tried first, at every l), least l1;
  4. wedge cells (unsplittable, l >= 5) through SP(l, delta) in the displacement picture:
     mu = 2(d-l)-1, sigma a permutation of [1,l] with {|2(sigma(w)-w)+mu|} = {1,3,...,2l-1};
     INV for mu < 0; REV for mu = 1; TT (tau_l) for mu = l; the CINV chain for 2mu <= l;
     block-reversal band families for l/2 < mu <= l by l mod 4;
     then Lemma P (sigma -> (pi, S/D)) and Lemma S (the four pair formulas) to the pairs.
  5. assemble + check, route counts, verdict; separate section: m-fold tight line (Table 1).
All family tables below are transcribed by hand from the class tables of the note (Appendix A).
"""
import sys
import os
import json
import time

HERE = os.path.dirname(os.path.abspath(__file__))  # the folder of this script
KILL = os.path.join(HERE, "KILL")  # an optional stop file: create it to interrupt a long run
OUTDIR = HERE  # routes_<L>.json is written beside this script


def kill_check():
    if os.path.exists(KILL):
        print("KILL file present -- stopping", flush=True)
        sys.exit(3)


# ============================================================================================
# 1. The checker (exact).
# ============================================================================================
def check_mfold(pairs, m, d, l):
    """None if `pairs` is an m-fold Langford sequence of order l, defect d; else a reason."""
    if not (isinstance(m, int) and isinstance(d, int) and isinstance(l, int)):
        return "non-integer parameters"
    if l < 1 or d < 1 or m < 1:
        return "parameters out of range"
    N = 2 * m * l
    if len(pairs) != m * l:
        return "wrong number of pairs: %d (want %d)" % (len(pairs), m * l)
    seen = bytearray(N + 1)
    cnt = [0] * l
    for pr in pairs:
        if len(pr) != 2:
            return "malformed pair %r" % (pr,)
        a, b = pr
        if type(a) is not int or type(b) is not int:
            return "non-integer entry in %r" % (pr,)
        if not (1 <= a < b <= N):
            return "pair %r out of range / unordered" % (pr,)
        if seen[a] or seen[b]:
            return "position reused in %r" % (pr,)
        seen[a] = 1
        seen[b] = 1
        p = b - a - d
        if p < 0 or p >= l:
            return "difference %d outside [%d,%d]" % (b - a, d, d + l - 1)
        cnt[p] += 1
    if sum(seen) != N:
        return "positions do not cover [1,%d]" % N
    for i, c in enumerate(cnt):
        if c != m:
            return "difference %d occurs %d times (want %d)" % (d + i, c, m)
    return None


def check_sigma(sig, l, mu):
    """sig is a list of length l+1 (index 0 unused). None iff sig solves SP in displacement form."""
    if len(sig) != l + 1:
        return "sigma length"
    if sorted(sig[1:]) != list(range(1, l + 1)):
        return "sigma not a permutation of [1,l]"
    xs = sorted(abs(2 * (sig[w] - w) + mu) for w in range(1, l + 1))
    if xs != list(range(1, 2 * l, 2)):
        return "|x| multiset is not {1,3,...,2l-1}"
    return None


# ============================================================================================
# 4a. Lemma P + Lemma S: sigma solving (l, mu) -> the 2l pairs of a two-fold sequence,
#     defect d = l + delta, delta = (mu+1)/2.
#     x_w = 2(sigma(w)-w)+mu, u = (|x_w|+1)/2, type S if x_w > 0 else D, pi(u) = w;
#     S: (l+1-pi(u), 2l+u), (2l+1-u, 3l+pi(u));   D: (l+1-pi(u), 2l+1-u), (2l+u, 3l+pi(u)).
# ============================================================================================
def sigma_to_pairs(sig, l, mu):
    out = []
    for w in range(1, l + 1):
        x = 2 * (sig[w] - w) + mu
        u = (abs(x) + 1) // 2
        if x > 0:
            out.append((l + 1 - w, 2 * l + u))
            out.append((2 * l + 1 - u, 3 * l + w))
        else:
            out.append((l + 1 - w, 2 * l + 1 - u))
            out.append((2 * l + u, 3 * l + w))
    return out


def inverse(sig):
    l = len(sig) - 1
    inv = [0] * (l + 1)
    for w in range(1, l + 1):
        inv[sig[w]] = w
    return inv


def tau(n):
    """tau_n (n odd): reverse [1,(n+1)/2] and [(n+3)/2, n].  Solves (n, n)."""
    h = (n + 1) // 2
    s = [0] * (n + 1)
    for i in range(1, h + 1):
        s[i] = h + 1 - i
    for i in range(h + 1, n + 1):
        s[i] = n + h + 1 - i
    return s


def reversal(n):
    return [0] + [n + 1 - w for w in range(1, n + 1)]


def cinv_step(s0, mu):
    """Lemma C then INV (sp-greedy claim 4): sigma0 solves (n, mu), 1 <= mu <= n ->
    sigma1(w) = sigma0(w)+mu (w <= n), sigma1(n+i) = tau_mu(i) solves (n+mu, -mu);
    its inverse solves (n+mu, mu)."""
    n = len(s0) - 1
    assert 1 <= mu <= n
    t = tau(mu)
    s1 = [0] * (n + mu + 1)
    for w in range(1, n + 1):
        s1[w] = s0[w] + mu
    for i in range(1, mu + 1):
        s1[n + i] = t[i]
    return inverse(s1)


# ============================================================================================
# 4b. Block-reversal shapes.  order = the block indices in target left-to-right order.
#     Sources [1,l] cut left to right into sizes n_0..n_{b-1}; block i maps its source interval
#     onto its target interval reversed: sigma(a_i + r) = c_i + n_i + 1 - r, r = 1..n_i
#     (a_i, c_i the 0-based starts).
# ============================================================================================
def build_shape(order, sizes, l):
    b = len(sizes)
    if sorted(order) != list(range(b)):
        raise ValueError("order is not a permutation of the blocks")
    for n in sizes:
        if type(n) is not int or n < 1:
            raise ValueError("block size %r not a positive integer" % (n,))
    if sum(sizes) != l:
        raise ValueError("sizes sum to %d, not l = %d" % (sum(sizes), l))
    a = [0] * b
    acc = 0
    for i in range(b):
        a[i] = acc
        acc += sizes[i]
    c = [0] * b
    acc = 0
    for i in order:
        c[i] = acc
        acc += sizes[i]
    s = [0] * (l + 1)
    for i in range(b):
        n = sizes[i]
        for r in range(1, n + 1):
            s[a[i] + r] = c[i] + n + 1 - r
    return s


def lin(form, l, mu):
    """form = (A, B, C, D) meaning (A*l + B*mu + C)/D, which must be an exact integer."""
    A, B, C, D = form
    num = A * l + B * mu + C
    if num % D:
        raise ValueError("non-integral size %r at (l,mu)=(%d,%d)" % (form, l, mu))
    return num // D


def ineqs_hold(ineqs, l, mu):
    return all(A * l + B * mu + C >= 0 for (A, B, C) in ineqs)


def idx(order_str):
    return tuple(int(ch) for ch in order_str)


# ---- l = 2 (mod 4): sp-greedy claim 6 (h = (mu+1)/2) ---------------------------------------
def fam_r2(l, mu):
    h = (mu + 1) // 2
    out = []
    if l % 4 == 2:
        q = (l - 2) // 4
        if q + 2 <= h and 2 * h <= 3 * q + 2:
            out.append(("FA", idx("23041"), [h - 1, q + 1, 3 * q + 3 - 2 * h, q, h - q - 1]))
    if l % 8 == 2:
        k = (l - 2) // 8
        if k >= 1 and 3 * k + 2 <= h <= 4 * k + 1:
            out.append(("FB2", idx("13042"),
                        [h - k - 1, k, 3 * k + 1, 8 * k + 3 - 2 * h, h - 3 * k - 1]))
    if l % 8 == 6:
        k = (l - 6) // 8
        if 3 * k + 4 <= h <= 4 * k + 3:
            out.append(("FB6", idx("13042"),
                        [h - k - 1, k + 1, 3 * k + 2, 8 * k + 7 - 2 * h, h - 3 * k - 3]))
        if mu == 6 * k + 5:
            out.append(("F4", idx("2031"), [3 * k + 2, 2 * k + 2, 2 * k + 1, k + 1]))
    return out


# ---- l = 0 (mod 4): band-r0 report + proofs_r0.txt ------------------------------------------
# Each entry: name, order, (mu modulus, residue), sizes as (A,B,C,D) = (A l + B mu + C)/D,
# full domain inequalities (A,B,C) meaning A l + B mu + C >= 0 (proofs_r0.txt "full domain").
R0_FAMILIES = [
    ("A1", "836720514", (4, 1),
     [(0, 1, -1, 4), (0, 0, 1, 1), (1, -1, 1, 4), (-1, 2, 2, 4), (0, 1, -1, 4), (0, 1, -1, 4),
      (3, -4, -4, 4), (1, 0, -4, 4), (0, 0, 1, 1)],
     [(-1, 2, -2), (-1, 2, 2), (0, 1, -5), (1, -1, -3), (1, -1, -1), (1, 0, -8), (1, 0, -2),
      (1, 0, -1), (2, -1, -3), (2, -1, -1), (2, -1, 1), (3, -4, -8)]),
    ("A3", "836720514", (4, 3),
     [(0, 1, 1, 4), (0, 0, 1, 1), (1, -1, -1, 4), (-1, 2, 2, 4), (0, 1, -3, 4), (0, 1, 1, 4),
      (3, -4, -4, 4), (1, 0, -4, 4), (0, 0, 1, 1)],
     [(-1, 2, -2), (-1, 2, 2), (0, 1, -7), (0, 1, -3), (1, -1, -5), (1, -1, -1), (1, 0, -8),
      (1, 0, -2), (1, 0, -1), (2, -1, -3), (2, -1, -1), (2, -1, 1), (3, -4, -8)]),
    ("U1", "57134026", (8, 1),
     [(2, -1, 1, 8), (-2, 3, -3, 8), (0, 1, 3, 4), (2, -1, 1, 8), (2, -1, -7, 8), (0, 0, 1, 1),
      (0, 1, -1, 4), (1, -1, -1, 2)],
     [(-2, 3, -11), (0, 1, -5), (0, 1, -1), (0, 1, 1), (1, -1, -3), (2, -1, -15), (2, -1, -7),
      (2, -1, -3), (2, -1, -1), (2, -1, 1), (2, -1, 5), (2, 1, -1)]),
    ("U3", "580364172", (8, 3),
     [(0, 1, -3, 4), (0, 1, 1, 4), (2, -1, 3, 8), (2, -1, -21, 8), (0, 0, 1, 1), (0, 0, 1, 1),
      (2, -1, 3, 8), (-2, 3, 7, 8), (1, -1, -1, 2)],
     [(-2, 3, -1), (0, 1, -7), (0, 1, -3), (0, 1, 1), (1, -1, -3), (2, -1, -29), (2, -1, -13),
      (2, -1, -9), (2, -1, -5), (2, -1, -1), (2, -1, 7), (2, 1, 1)]),
    ("U5", "47035162", (8, 5),
     [(0, 1, -1, 4), (0, 1, 3, 4), (2, -1, -3, 8), (2, -1, -3, 8), (0, 0, 1, 1), (2, -1, -3, 8),
      (-2, 3, 1, 8), (1, -1, -1, 2)],
     [(-2, 3, -7), (0, 1, -5), (0, 1, -1), (0, 1, 1), (1, -1, -3), (2, -1, -11), (2, -1, -3),
      (2, -1, -1), (2, -1, 1), (2, -1, 5), (2, 1, 3)]),
    ("U7", "162470835", (8, 7),
     [(0, 1, 1, 8), (0, 1, 1, 8), (0, 1, 1, 8), (2, -1, -1, 4), (-4, 5, -3, 8), (0, 1, 1, 8),
      (1, -1, 0, 1), (1, -1, 1, 2), (-4, 5, -3, 8)],
     [(-4, 5, -11), (-4, 5, 1), (0, 1, -7), (0, 1, 1), (1, -1, -1), (1, -1, 1), (2, -1, -5),
      (2, -1, 1), (4, -3, 1), (4, -1, 3)]),
    ("V", "805734126", (4, 3),
     [(1, -1, 3, 4), (0, 1, -3, 4), (0, 1, 1, 4), (4, -5, 7, 4), (-2, 3, -5, 4), (-3, 5, -7, 4),
      (-1, 2, -2, 4), (4, -5, 7, 4), (1, -1, -1, 4)],
     [(-3, 5, -11), (-2, 3, -9), (-2, 3, -7), (-2, 3, -3), (-1, 2, -6), (-1, 2, -2), (0, 1, -7),
      (0, 1, -3), (0, 1, -1), (1, -1, -5), (1, -1, -1), (1, -1, 2), (1, 0, 2), (2, -1, 1),
      (2, -1, 3), (3, -3, 5), (4, -5, 3)]),
    ("T", "2360415", (8, 3),
     [(0, 1, 1, 4), (0, 1, -3, 8), (8, -7, 5, 8), (-8, 9, -3, 8), (0, 1, -3, 8), (0, 1, 1, 4),
      (1, -1, 0, 1)],
     [(-8, 9, -11), (-4, 5, 1), (0, 1, -11), (0, 1, -3), (1, -1, -1), (1, -1, 1), (2, -1, 1),
      (4, -3, -3), (4, -3, 1), (4, -3, 5), (4, -1, 3), (8, -7, -3)]),
]
# band-r0's sporadic cells (l, mu): no family holds them; the sigmas are NOT transcribed
# (they live only in band-r0's code) -- this file finds them by its own exact search.
R0_SPORADIC = [(8, 5), (8, 7), (12, 9), (12, 11), (16, 11), (20, 15), (24, 17), (32, 23)]


def fam_r0(l, mu):
    out = []
    if l % 4 != 0:
        return out
    for name, order, (mod, res), sizes, ineqs in R0_FAMILIES:
        if mu % mod == res and ineqs_hold(ineqs, l, mu):
            out.append((name, idx(order), [lin(f, l, mu) for f in sizes]))
    return out


# ---- l = 1 (mod 4): band-r1 report + classtables_r1.txt -------------------------------------
R1_BASES = {  # explicit sigmas printed in band-r1's report (claim 4), from sp-greedy's search
    (5, 3): [3, 5, 2, 4, 1],
    (9, 5): [6, 5, 9, 8, 1, 7, 4, 3, 2],
}


def fam_r1(l, mu):
    out = []
    if l % 4 != 1:
        return out
    if mu == l - 2 and l >= 9:
        out.append(("FT", idx("513042"),
                    [lin(f, l, mu) for f in [(1, 0, -1, 4), (1, 0, -5, 4), (1, 0, -1, 4),
                                             (0, 0, 1, 1), (1, 0, -1, 4), (0, 0, 1, 1)]]))
    if 2 * mu == l + 1:
        if l % 8 == 1 and l >= 17:
            p = (l - 1) // 8
            out.append(("FL1", idx("6024513"), [1, p, p - 1, 2 * p, p, p + 1, 2 * p]))
        if l % 8 == 5 and l >= 13:
            p = (l - 5) // 8
            out.append(("FL5", idx("513402"), [p + 1, p + 1, 2 * p + 1, p, p + 1, 2 * p + 1]))
    if mu % 4 == 1 and 2 * mu >= l + 5 and mu <= l - 4:
        out.append(("FA1", idx("71340526"),
                    [lin(f, l, mu) for f in [(0, 1, -1, 4), (0, 1, -5, 4), (1, 0, -1, 4),
                                             (1, -1, 0, 4), (1, -1, 4, 4), (-1, 2, -1, 4),
                                             (0, 0, 1, 1), (1, -1, 0, 2)]]))
    if mu % 4 == 3 and 2 * mu >= l + 5 and mu <= l - 6:
        out.append(("FA3", idx("6134052"),
                    [lin(f, l, mu) for f in [(0, 1, 1, 4), (0, 1, 1, 4), (1, 0, -1, 4),
                                             (1, -1, -2, 4), (1, -1, 2, 4), (-1, 2, -1, 4),
                                             (1, -1, 0, 2)]]))
    return out


# ---- l = 3 (mod 4): band-r3 report (l = 4q+3, t = (l-mu)/2, band 0 <= t <= q) ---------------
def fam_r3(l, mu):
    out = []
    if l % 4 != 3:
        return out
    q = (l - 3) // 4
    t = (l - mu) // 2
    if t == 1 and q >= 1:
        out.append(("R3T1", idx("513042"), [q, q, q + 1, 1, q, 1]))
    if t % 2 == 1 and 3 <= t <= q:
        out.append(("R3O", idx("6134052"),
                    [(2 * q + 1 - t) // 2, (2 * q + 1 - t) // 2, q + 1, (t - 1) // 2, (t + 1) // 2,
                     q + 1 - t, t]))
    if t % 2 == 0 and 2 <= t <= q - 1:
        out.append(("R3E", idx("70245163"),
                    [1, q + 1 - t // 2, q - t // 2, q, t // 2, t // 2 + 1, q - t, t]))
    if t % 2 == 0 and 2 * q + 2 <= 3 * t and t <= q:
        out.append(("R3Q", idx("6024513"),
                    [2 * q + 1 - 2 * t, q + 1 - t // 2, (3 * t - 2 * q) // 2, t, q - t // 2,
                     q + 1 - t // 2, t]))
    return out


FAMILY_ORDER = {0: fam_r0, 1: fam_r1, 2: fam_r2, 3: fam_r3}

# (7, 3): the explicit base of Theorem R (sp-greedy claim 5), used when the chain base is (4, 3).
SIGMA_7_3 = [6, 4, 7, 3, 5, 2, 1]


# ============================================================================================
# A small exact search (Algorithm X, MRV, deterministic), used ONLY for band-r0's sporadic cells.
# Items: class k, source w, target s.  Option (w, s) covers w, s and k = (|2(s-w)+mu|+1)/2 <= l.
# ============================================================================================
def sp_search(l, mu, node_cap=5_000_000):
    opts = []
    for w in range(1, l + 1):
        for s in range(1, l + 1):
            k = (abs(2 * (s - w) + mu) + 1) // 2
            if k <= l:
                opts.append((("w", w), ("s", s), ("k", k)))
    items = [("k", k) for k in range(l, 0, -1)] + [("w", w) for w in range(1, l + 1)] + \
            [("s", s) for s in range(1, l + 1)]
    rank = {it: i for i, it in enumerate(items)}
    X = {it: set() for it in items}
    for j, o in enumerate(opts):
        for it in o:
            X[it].add(j)
    nodes = [0]
    sol = []

    def select(j):
        cols = []
        for it in opts[j]:
            for i in X[it]:
                for it2 in opts[i]:
                    if it2 != it:
                        X[it2].discard(i)
            cols.append(X.pop(it))
        return cols

    def deselect(j, cols):
        for it in reversed(opts[j]):
            X[it] = cols.pop()
            for i in X[it]:
                for it2 in opts[i]:
                    if it2 != it:
                        X[it2].add(i)

    def solve():
        if not X:
            return True
        nodes[0] += 1
        if nodes[0] > node_cap:
            raise RuntimeError("node cap %d hit at (%d,%d)" % (node_cap, l, mu))
        if nodes[0] % 4096 == 0:
            kill_check()
        it = min(X, key=lambda z: (len(X[z]), rank[z]))
        for j in sorted(X[it]):
            sol.append(j)
            cols = select(j)
            if solve():
                return True
            deselect(j, cols)
            sol.pop()
        return False

    if not solve():
        return None, nodes[0]
    s = [0] * (l + 1)
    for j in sol:
        (_, w), (_, t), _ = opts[j]
        s[w] = t
    return s, nodes[0]


SPORADIC_CACHE = {}


# ============================================================================================
# 4c. SP dispatcher.
# ============================================================================================
def band_sigma(l, mu):
    """l/2 < mu <= l, mu odd, l >= 5.  Returns (sigma, family name)."""
    if mu == l:
        return tau(l), "TT"
    fams = FAMILY_ORDER[l % 4](l, mu)
    if fams:
        name, order, sizes = fams[0]
        return build_shape(order, sizes, l), name
    if l % 4 == 1 and (l, mu) in R1_BASES:
        return [0] + R1_BASES[(l, mu)], "BASE-r1(%d,%d)" % (l, mu)
    if l % 4 == 0 and (l, mu) in R0_SPORADIC:
        if (l, mu) not in SPORADIC_CACHE:
            s, nodes = sp_search(l, mu)
            if s is None:
                raise RuntimeError("search found no sigma at sporadic (%d,%d)" % (l, mu))
            SPORADIC_CACHE[(l, mu)] = (s, nodes)
        return list(SPORADIC_CACHE[(l, mu)][0]), "SPORADIC-search"
    raise LookupError("UNCOVERED band cell (l,mu)=(%d,%d)" % (l, mu))


def solve_sp(l, mu):
    """Any cone cell -l <= mu <= l (mu odd), l >= 5 or a closed-form small case.
    Returns (sigma, route, family_key)."""
    assert mu % 2 == 1 and -l <= mu <= l
    if mu < 0:
        s, r, key = solve_sp(l, -mu)
        return inverse(s), "INV(" + r + ")", key
    if mu == 1:
        return reversal(l), "REV", "REV"
    if mu == l:
        return tau(l), "TT", "TT"
    if 2 * mu <= l:
        l0 = mu + (l - mu) % mu
        if l0 == mu:
            s, rb = tau(mu), "TT"
        elif (l0, mu) == (4, 3):
            l0 = 7
            s, rb = [0] + SIGMA_7_3, "BASE(7,3)"
        else:
            s, rb = band_sigma(l0, mu)
        steps = (l - l0) // mu
        for _ in range(steps):
            s = cinv_step(s, mu)
        return s, "CINV[%s@(%d,%d)]x%d" % (rb, l0, mu, steps), "CINV"
    s, name = band_sigma(l, mu)
    return s, "BAND:" + name, name


# ============================================================================================
# 2. Literal census witnesses (census-cpsat/witnesses_m2.jsonl, engine cpsat-ortools9.15-nw1),
#    keyed (l, d).  Re-checked at start-up; used only at unsplittable cells with l <= 4.
# ============================================================================================
CENSUS = {
    (1, 1): [[1, 2], [3, 4]],
    (1, 2): [[1, 3], [2, 4]],
    (2, 1): [[1, 2], [3, 5], [4, 6], [7, 8]],
    (2, 2): [[1, 3], [2, 5], [4, 7], [6, 8]],
    (2, 3): [[1, 4], [2, 6], [3, 7], [5, 8]],
    (3, 1): [[1, 2], [3, 4], [5, 7], [6, 9], [8, 11], [10, 12]],
    (3, 2): [[1, 4], [2, 6], [3, 7], [5, 8], [9, 11], [10, 12]],
    (3, 3): [[1, 4], [2, 6], [3, 8], [5, 10], [7, 11], [9, 12]],
    (3, 4): [[1, 5], [2, 7], [3, 9], [4, 10], [6, 11], [8, 12]],
    (3, 5): [[1, 8], [2, 7], [3, 9], [4, 10], [5, 12], [6, 11]],
    (4, 1): [[1, 4], [2, 3], [5, 7], [6, 10], [8, 11], [9, 13], [12, 14], [15, 16]],
    (4, 2): [[1, 3], [2, 7], [4, 8], [5, 9], [6, 11], [10, 13], [12, 15], [14, 16]],
    (4, 3): [[1, 5], [2, 6], [3, 8], [4, 9], [7, 13], [10, 16], [11, 14], [12, 15]],
    (4, 4): [[1, 5], [2, 7], [3, 9], [4, 11], [6, 13], [8, 14], [10, 15], [12, 16]],
    (4, 5): [[1, 6], [2, 8], [3, 10], [4, 12], [5, 13], [7, 14], [9, 15], [11, 16]],
    (4, 6): [[1, 7], [2, 11], [3, 10], [4, 12], [5, 13], [6, 15], [8, 14], [9, 16]],
}
LITERALS_USED = set()
CENSUS_SMALL = False  # set by --census-small


# ============================================================================================
# 3. Splitting.
# ============================================================================================
def least_split(d, l):
    """Least l1 in [1, l-1] with 3 l1 >= 2d-1 and 3(l-l1) >= 2(d+l1)-1, else None."""
    lo = max(1, -(-(2 * d - 1) // 3))
    # second condition: 5 l1 <= 3l - 2d + 1
    hi = (3 * l - 2 * d + 1) // 5
    hi = min(hi, l - 1)
    return lo if lo <= hi else None


def build(d, l):
    """Pairs for the two-fold cell (d, l), and its top-level route string."""
    l1 = least_split(d, l)
    if l1 is not None:
        A, _ = build(d, l1)
        B, _ = build(d + l1, l - l1)
        sh = 4 * l1
        return A + [(a + sh, b + sh) for (a, b) in B], "CONCAT(l1=%d)" % l1
    mu = 2 * (d - l) - 1
    if l <= 4:
        # Unsplittable small cells.  By default the closed forms REV / TT (and INV) are used where
        # they apply (they are valid for every l >= 1), so a literal is used only where SP(l, mu)
        # has no closed form here: (d, l) = (3, 4) and (6, 4), i.e. SP(4, -3) and SP(4, 3), which
        # are empty (wedge-B Lemma I / sp-greedy claim 3).  --census-small: literal at every
        # unsplittable l <= 4 cell (the letter of the brief's step 2).
        if CENSUS_SMALL or not (mu in (1, -1) or abs(mu) == l):
            LITERALS_USED.add((l, d))
            return [tuple(p) for p in CENSUS[(l, d)]], "LITERAL"
    if not (-l <= mu <= l):
        raise AssertionError("unsplittable cell outside the wedge: (d,l)=(%d,%d)" % (d, l))
    s, r, _ = solve_sp(l, mu)
    return sigma_to_pairs(s, l, mu), "SP:" + r


def classify(route):
    """(category, detail, via_inv).  category in literal / concatenation / SP band family /
    CINV chain / SP REV / SP TT; detail = family name or chain base."""
    if route.startswith("CONCAT"):
        return "concatenation", "", False
    if route == "LITERAL":
        return "literal", "", False
    r = route[3:]
    inv = r.startswith("INV(")
    if inv:
        r = r[4:-1]
    if r.startswith("CINV"):
        base = r.split("[")[1].split("@")[0]
        base = "BASE-r1" if base.startswith("BASE-r1") else base
        return "CINV chain", base, inv
    if r.startswith("BAND:"):
        fam = r[5:]
        fam = "BASE-r1" if fam.startswith("BASE-r1") else fam
        return "SP band family", fam, inv
    return "SP " + r, r, inv


# ============================================================================================
# Section B: band census -- every band cell l/2 < mu <= l with 5 <= l <= LB routed through
# band_sigma, sigma checked, first-family counts (compare with the note's coverage tables).
# ============================================================================================
EXPECTED_400 = {  # first-family counts at l <= 400 (the note's coverage tables)
    0: {"A1": 1225, "A3": 1225, "U1": 635, "U3": 612, "U5": 637, "U7": 500, "V": 159, "T": 48,
        "SPORADIC-search": 8},
    1: {"BASE-r1": 2, "TT": 99, "FT": 98, "FL5": 49, "FA1": 2401, "FL1": 48, "FA3": 2352},
    2: {"FA": 2450, "FB6": 1225, "FB2": 1225, "F4": 50},
    3: {"TT": 99, "R3T1": 99, "R3O": 2401, "R3E": 2401, "R3Q": 49},
}


REPS = {}  # one representative domain cell per family (l >= 20), for the mutation controls


def mutation_controls():
    """Negative controls: perturb each family's sizes (move one unit between adjacent blocks) and
    its order (swap the first two target slots) at a representative cell; the sigma check must
    reject every mutant, and the pair checker must reject a lifted witness with two right
    endpoints swapped."""
    caught = total = 0
    for fname, (l, mu, order, sizes) in sorted(REPS.items()):
        muts = []
        for i in range(len(sizes) - 1):
            if sizes[i + 1] > 1:
                s2 = list(sizes)
                s2[i] += 1
                s2[i + 1] -= 1
                muts.append((order, s2))
                break
        o2 = list(order)
        o2[0], o2[1] = o2[1], o2[0]
        muts.append((tuple(o2), sizes))
        for (o, s) in muts:
            total += 1
            if check_sigma(build_shape(o, s, l), l, mu) is not None:
                caught += 1
        good = sigma_to_pairs(build_shape(order, sizes, l), l, mu)
        d = l + (mu + 1) // 2
        total += 1
        if check_mfold(good, 2, d, l) is None:
            bad = list(good)
            j = next(j for j in range(1, len(bad)) if bad[j][1] - bad[j][0] != bad[0][1] - bad[0][0])
            (a0, b0), (a1, b1) = bad[0], bad[j]
            bad[0], bad[j] = (a0, b1), (a1, b0)
            if check_mfold(bad, 2, d, l) is not None:
                caught += 1
    return caught, total


def band_census(LB):
    first = {r: {} for r in range(4)}
    first400 = {r: {} for r in range(4)}
    alldom = {}
    fails = []
    ncells = 0
    for l in range(5, LB + 1):
        kill_check()
        for mu in range(l // 2 + 1, l + 1):
            if mu % 2 == 0 or not (2 * mu > l):
                continue
            ncells += 1
            try:
                s, name = band_sigma(l, mu)
            except Exception as ex:  # noqa: BLE001 -- report and continue
                fails.append((l, mu, str(ex)))
                continue
            err = check_sigma(s, l, mu)
            if err:
                fails.append((l, mu, name + ": " + err))
            key = "BASE-r1" if name.startswith("BASE-r1") else name
            first[l % 4][key] = first[l % 4].get(key, 0) + 1
            if l <= 400:
                first400[l % 4][key] = first400[l % 4].get(key, 0) + 1
            # every family whose domain holds the cell (full-domain counts), each checked
            if mu != l:
                for fname, order, sizes in FAMILY_ORDER[l % 4](l, mu):
                    alldom[fname] = alldom.get(fname, 0) + 1
                    if fname not in REPS and l >= 20:
                        REPS[fname] = (l, mu, order, list(sizes))
                    err2 = check_sigma(build_shape(order, sizes, l), l, mu)
                    if err2:
                        fails.append((l, mu, fname + " (domain sweep): " + err2))
    return ncells, first, first400, alldom, fails


# ============================================================================================
# Section C: the m-fold tight line, m copies of Table 1 (arXiv:2112.04265 v1, p. 4):
#   Table 1, L_{2d0-1}^{d0}: i = d0+2r: (d0-r, 2d0+r), 0 <= r <= d0-1;
#                            i = d0+2r+1: (2d0-1-r, 3d0+r), 0 <= r <= d0-2.
#   It is tight (left ends [1,n], right ends [n+1,2n], n = 2d0-1).  The m copies are laid side by
#   side in the straddle picture: copy j pairs (a + j n, m n + (b - n) + j n).
#   Result: m-fold Langford of order n and defect ((2m-1) n + 1)/2.
# ============================================================================================
def table1(d0):
    rows = []
    for r in range(0, d0):
        rows.append((d0 - r, 2 * d0 + r))
    for r in range(0, d0 - 1):
        rows.append((2 * d0 - 1 - r, 3 * d0 + r))
    return rows


def mfold_tight(m, n):
    d0 = (n + 1) // 2
    rows = table1(d0)
    out = []
    for j in range(m):
        for a, b in rows:
            out.append((a + j * n, m * n + (b - n) + j * n))
    return out, ((2 * m - 1) * n + 1) // 2


# ============================================================================================
# main
# ============================================================================================
def main():
    global CENSUS_SMALL
    if len(sys.argv) < 2:
        print("usage: python verify.py L [--no-routes] [--census-small]")
        return 2
    L = int(sys.argv[1])
    CENSUS_SMALL = "--census-small" in sys.argv
    t0 = time.time()
    ok = True
    print("verify.py (a two-fold Langford sequence at every in-bound cell) -- L = %d%s" %
          (L, "  [--census-small: literal at every unsplittable l <= 4 cell]" if CENSUS_SMALL
           else "  [default: literal only where no closed form applies]"), flush=True)
    print("python %s" % sys.version.split()[0])

    # --- self-tests of the checker (negative controls) ---
    good = CENSUS[(3, 5)]
    assert check_mfold([tuple(p) for p in good], 2, 5, 3) is None
    bad1 = [tuple(p) for p in good]
    bad1[0] = (1, 9)
    assert check_mfold(bad1, 2, 5, 3) is not None
    assert check_mfold([tuple(p) for p in good], 2, 4, 3) is not None
    assert check_mfold([tuple(p) for p in good][:-1], 2, 5, 3) is not None
    assert check_sigma([0] + SIGMA_7_3, 7, 3) is None
    assert check_sigma([0] + SIGMA_7_3, 7, 5) is not None
    print("[self-test] checker negative controls: ok")

    # --- literals: re-check all 16 census witnesses ---
    lit_bad = 0
    for (l, d), prs in sorted(CENSUS.items()):
        e = check_mfold([tuple(p) for p in prs], 2, d, l)
        if e:
            lit_bad += 1
            print("  census witness (l,d)=(%d,%d) FAILS: %s" % (l, d, e))
    print("[literals] census witnesses l <= 4 re-checked: %d, failures %d" % (len(CENSUS), lit_bad))
    ok &= (lit_bad == 0)
    # explicit SP bases transcribed from the reports
    for (l, mu), s in list(R1_BASES.items()) + [((7, 3), SIGMA_7_3)]:
        e = check_sigma([0] + s, l, mu)
        print("[bases] explicit sigma (l,mu)=(%d,%d) %s: %s" % (l, mu, s, "ok" if e is None else e))
        ok &= (e is None)

    # --- sporadic cells by search ---
    for (l, mu) in R0_SPORADIC:
        kill_check()
        if FAMILY_ORDER[0](l, mu):
            print("[sporadic] NOTE (%d,%d) is inside a family domain: %s" %
                  (l, mu, [f[0] for f in FAMILY_ORDER[0](l, mu)]))
        ts = time.time()
        s, name = band_sigma(l, mu)
        e = check_sigma(s, l, mu)
        print("[sporadic] (l,mu)=(%d,%d) %s nodes=%d %.2fs sigma=%s %s" %
              (l, mu, name, SPORADIC_CACHE.get((l, mu), (None, 0))[1], time.time() - ts,
               s[1:], "ok" if e is None else e))
        ok &= (e is None)

    # --- Section A: every in-bound cell ---
    cat_counts = {}
    fam_counts = {}
    routes = []
    fails = []
    ncell = 0
    for l in range(1, L + 1):
        kill_check()
        for d in range(1, (3 * l + 1) // 2 + 1):
            ncell += 1
            try:
                prs, route = build(d, l)
            except Exception as ex:  # noqa: BLE001
                fails.append((l, d, "construction error: %s" % ex))
                continue
            e = check_mfold(prs, 2, d, l)
            if e:
                fails.append((l, d, route + ": " + e))
            cat, detail, inv = classify(route)
            cc = cat_counts.setdefault(cat, [0, 0])
            cc[1 if inv else 0] += 1
            if detail:
                fc = fam_counts.setdefault((cat, detail), [0, 0])
                fc[1 if inv else 0] += 1
            routes.append({"l": l, "d": d, "mu": 2 * (d - l) - 1, "route": route})
        if l % 50 == 0 or l == L:
            print("  ... l = %d done, %d cells, %d failures, %.1fs" %
                  (l, ncell, len(fails), time.time() - t0), flush=True)
    print("[A] in-bound cells 1 <= l <= %d, 1 <= d <= floor((3l+1)/2): %d; verified %d; failures %d"
          % (L, ncell, ncell - len(fails), len(fails)))
    for f in fails[:40]:
        print("   FAIL", f)
    print("[A] cells by top-level route (columns: total = mu > 0 direct + mu < 0 via INV):")
    for k in ["literal", "concatenation", "SP REV", "SP TT", "SP band family", "CINV chain"]:
        v = cat_counts.get(k, [0, 0])
        print("   %-26s %8d = %7d + %7d" % (k, v[0] + v[1], v[0], v[1]))
    extra = [k for k in cat_counts if k not in ("literal", "concatenation", "SP REV", "SP TT",
                                                "SP band family", "CINV chain")]
    for k in extra:
        print("   UNEXPECTED CATEGORY %s %s" % (k, cat_counts[k]))
    print("   %-26s %8d" % ("total", sum(a + b for a, b in cat_counts.values())))
    print("[A] SP band family cells by family, and CINV-chain cells by chain base (direct + INV):")
    for (cat, det) in sorted(fam_counts):
        if cat in ("SP band family", "CINV chain"):
            v = fam_counts[(cat, det)]
            print("   %-16s %-18s %8d = %7d + %7d" % (cat.split()[0] if cat == "CINV chain"
                                                     else "band", det, v[0] + v[1], v[0], v[1]))
    print("[A] literal census witnesses used, as (l, d) (unsplittable cells, l <= 4): %d: %s"
          % (len(LITERALS_USED), sorted(LITERALS_USED)))
    ok &= (len(fails) == 0)

    if "--no-routes" not in sys.argv:
        fn = OUTDIR + "/routes_%d.json" % L
        with open(fn, "w") as fh:
            json.dump(routes, fh, separators=(",", ":"))
        print("[A] routes written to %s" % fn)

    # --- Section B: band census ---
    LB = max(L, 400)
    nb, first, first400, alldom, bfails = band_census(LB)
    print("[B] band cells l/2 < mu <= l, 5 <= l <= %d: %d; sigma failures/uncovered %d"
          % (LB, nb, len(bfails)))
    for f in bfails[:40]:
        print("   FAIL", f)
    for r in range(4):
        print("   l = %d (mod 4) first-family counts: %s" % (r, dict(sorted(first[r].items()))))
    print("   full-domain counts (every family holding the cell, each checked): %s"
          % dict(sorted(alldom.items())))
    ok &= (len(bfails) == 0)
    mism = []
    for r in range(4):
        got, exp = first400[r], EXPECTED_400[r]
        for k in sorted(set(exp) | set(got)):
            if got.get(k, 0) != exp.get(k, 0):
                mism.append((r, k, got.get(k, 0), exp.get(k, 0)))
    print("[B] l <= 400 first-family counts vs the note's coverage tables: %s"
          % ("all match" if not mism else "MISMATCH (r, family, here, printed) %s" % mism))
    mc, mt = mutation_controls()
    print("[B] negative controls (mutated family sizes/orders at %d families; swapped endpoints in "
          "a lifted witness): %d of %d mutants rejected" % (len(REPS), mc, mt))

    # --- Section C: m-fold tight line ---
    cfail = 0
    ccount = 0
    for m in range(1, 7):
        for n in range(1, 42, 2):
            kill_check()
            prs, d = mfold_tight(m, n)
            ccount += 1
            e = check_mfold(prs, m, d, n)
            if e:
                cfail += 1
                print("   tight FAIL m=%d l=%d d=%d: %s" % (m, n, d, e))
            if 2 * d - 1 != (2 * m - 1) * n:
                cfail += 1
                print("   tight cell not on the counting line m=%d l=%d d=%d" % (m, n, d))
    print("[C] m-fold tight line, m copies of Table 1, 1 <= m <= 6, odd l <= 41: %d cells, "
          "failures %d" % (ccount, cfail))
    ok &= (cfail == 0)

    el = time.time() - t0
    print("elapsed %.1f s" % el)
    print("VERDICT: %s" % ("ALL VERIFIED -- every in-bound cell with l <= %d has a checked two-fold "
                           "Langford sequence" % L if ok else "FAILURES PRESENT"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
