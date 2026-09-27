#!/usr/bin/env python3
"""The bounds of L2/Residue.lean, L2/Forced.lean and L2/Straddle.lean against brute-force existence.

An m-fold Langford sequence of order l and defect d is a partition of [1, 2ml] into pairs (a, a + p),
m pairs for each p in [d, d + l - 1]; the pairs are a chosen partition, so chains are allowed (this
is Langford.IsLangford). Every pair system is enumerated by depth-first search on the leftmost
empty position. Standard library only, exact integers.

Checked on every cell with m <= 4, l <= 6, 2ml <= 20 and d up to one past the counting line:
  (R)  the residue bound:  r(T - r) <= m * sum |p - T|, r = ml mod T, for every T in [1, 2ml + 2],
       at every realized cell;
  (F)  the forced-endpoint bound  6mld + ml <= 4d^2 + 2(ml)^2 + ml^2  at every realized cell;
  (S)  rigidity: for every sequence, 2d + l = 2ml + 1 iff every i <= ml has ml < i + s(i);
  (P)  every position <= d is a left end and every left end is <= 2ml - d, for every sequence;
  (W)  the closed form of sum |p - T| for d <= T <= d + l - 1.
Then the uniform families for 3 <= m <= 400: (3m - 3, 3) meets counting and parity and fails (F)
exactly when m >= 4; (2m - 1, 2) meets counting, meets parity exactly for even m, and fails (F) for
every m >= 3; and the two example cells (7, 9, 4) at T = 11 and (19, 12, 3) at T = 13.
At m = 2, where every in-bound cell is realized, (F) is checked for l <= 400 and (R) for l <= 60
(every T <= 4l + 2); with --full, (R) runs to l <= 400 as well (about half an hour).
"""
import sys

sys.setrecursionlimit(10000)


def sequences(m, d, l):
    """Yield every m-fold Langford sequence of the cell as (values s[1..2ml], left-end flags)."""
    n = m * l
    N = 2 * n
    s = [0] * (N + 1)
    left = [0] * (N + 1)
    remaining = {p: m for p in range(d, d + l)}

    def rec():
        i = 1
        while i <= N and s[i]:
            i += 1
        if i > N:
            yield tuple(s[1:]), tuple(left[1:])
            return
        for p in range(d, d + l):
            if remaining[p] and i + p <= N and not s[i + p]:
                s[i] = s[i + p] = p
                left[i] = 1
                remaining[p] -= 1
                yield from rec()
                remaining[p] += 1
                left[i] = 0
                s[i] = s[i + p] = 0

    yield from rec()


def abs_sum(d, l, T):
    return sum(abs(p - T) for p in range(d, d + l))


def window_closed(d, l, T):
    u, v = T - d, d + l - 1 - T
    return (u * (u + 1) + v * (v + 1)) // 2


def forced(m, d, l):
    n = m * l
    return 6 * n * d + n <= 4 * d * d + 2 * n * n + n * l


def residue_ok(m, d, l, Tmax=None):
    n = m * l
    Tmax = Tmax or 2 * n + 2
    for T in range(1, Tmax + 1):
        r = n % T
        if r * (T - r) > m * abs_sum(d, l, T):
            return False, T
    return True, None


def counting(m, d, l):
    return 2 * d + l <= 2 * m * l + 1


def parity(m, d, l):
    return m % 2 == 0 or (l * (2 * d + l + 1)) % 4 == 0


def main(full):
    cells = exist = residue_kills = forced_kills = 0
    for m in range(1, 5):
        for l in range(1, 7):
            if 2 * m * l > 20:
                continue
            for d in range(1, (2 * m * l + 1 - l) // 2 + 2):
                cells += 1
                seqs = list(sequences(m, d, l))
                ex = bool(seqs)
                exist += ex
                fo = forced(m, d, l)
                ro, badT = residue_ok(m, d, l)
                if ex:
                    assert fo, ("forced-endpoint bound violated at a realized cell", m, d, l)
                    assert ro, ("residue bound violated at a realized cell", m, d, l, badT)
                    tight = 2 * d + l == 2 * m * l + 1
                    n = m * l
                    for s, left in seqs:
                        straddle = all(n < i + s[i - 1] for i in range(1, n + 1))
                        assert straddle == tight, ("rigidity fails", m, d, l, s)
                        for i in range(1, d + 1):
                            assert left[i - 1] == 1, (m, d, l, s, i)
                        for i in range(1, 2 * n + 1):
                            if left[i - 1]:
                                assert i <= 2 * n - d
                else:
                    residue_kills += not ro
                    forced_kills += not fo
                for T in range(d, d + l):
                    assert window_closed(d, l, T) == abs_sum(d, l, T)
    print(f"grid m <= 4, l <= 6, 2ml <= 20: {cells} cells, {exist} realized; among the empty cells the "
          f"residue bound rejects {residue_kills}, the forced-endpoint bound {forced_kills}")

    for m in range(3, 401):
        d, l = 3 * m - 3, 3
        assert counting(m, d, l) and parity(m, d, l)
        assert (2 * m - 1) * l - 2 * d + 1 == 4
        assert forced(m, d, l) == (m <= 3), m
        d2, l2 = 2 * m - 1, 2
        assert counting(m, d2, l2)
        assert parity(m, d2, l2) == (m % 2 == 0)
        assert not forced(m, d2, l2), m
        n = m * l
        r = n % d
        assert (r * (d - r) <= m * abs_sum(d, l, d)) == (m <= 3)
        r2 = (m * l2) % d2
        assert (r2 * (d2 - r2) <= m * abs_sum(d2, l2, d2)) == (m <= 2), m
    print("uniform families (3m - 3, 3) and (2m - 1, 2), 3 <= m <= 400: as stated")

    for m in range(1, 30):
        for l in range(1, 30):
            for d in range(1, m * l + 1):
                n = m * l
                e = 2 * n - 2 * d - l + 1
                assert 4 * (n - d) ** 2 - n * e == 4 * d * d - 6 * n * d + 2 * n * n + n * (l - 1)
    m, d, l = 7, 9, 4
    assert counting(m, d, l) and parity(m, d, l)
    assert 7 * abs_sum(9, 4, 11) == 28 and (28 % 11) * (11 - 28 % 11) == 30
    assert forced(m, d, l)
    m, d, l = 19, 12, 3
    assert counting(m, d, l) and parity(m, d, l)
    assert 19 * abs_sum(12, 3, 13) == 38 and (57 % 13) * (13 - 57 % 13) == 40
    print("the cells (7, 9, 4) at T = 11 and (19, 12, 3) at T = 13 fail the residue bound; (7, 9, 4) passes the "
          "forced-endpoint bound")

    Lres = 400 if full else 60
    for l in range(1, 401):
        for d in range(1, (3 * l + 1) // 2 + 1):
            assert forced(2, d, l), (d, l)
            if l <= Lres:
                ok, T = residue_ok(2, d, l, Tmax=4 * l + 2)
                assert ok, (d, l, T)
    print(f"m = 2: the forced-endpoint bound holds at every in-bound cell with l <= 400, the residue bound "
          f"(every T <= 4l + 2) with l <= {Lres}")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main(full="--full" in sys.argv[1:])
