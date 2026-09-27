#!/usr/bin/env python3
"""The certificate family of the note, in exact integer arithmetic.

For a cell (m, d, l) and an integer T >= 1 put n = ml, r = n mod T, S(T) = sum_{p=d}^{d+l-1} |p - T| and
H(T) = m S(T) - r(T - r), half the minimum over the two signs of the centred triangular-wave certificate
at T (the residue bound of L2/Residue.lean says H(T) >= 0 whenever a sequence exists). For j >= 1 put
J = j(j + 1), a = m + J, b = m((2j + 2)l + 2d - 1), C = m^2 l^2 + m d^2 + m(l - 1)d + ml(l - 1)/2 and
F_j(T) = aT^2 - bT + C; the note proves F_j(T) >= H(T) for every integer T >= 1, that t_j = floor((b + a)/(2a))
minimizes F_j over the integers with 4aF_j(t_j) = 4aC - b^2 + rho_j^2 (rho_j = b - 2a t_j), and that for
l >= 2 some certificate of the family is negative exactly when the counting bound fails or F_j(t_j) < 0 for
some j with J(l^2 - 1) < ml^2. This script checks those statements on the grid 1 <= m <= 20, 1 <= l <= 20,
1 <= d <= floor(((2m - 1)l + 1)/2) + 2 (42,900 triples): on every triple the finite test agrees with a direct
scan of H(T) over 1 <= T <= max(ml, d + l - 1); for the negative cases with m <= 10 and l <= 8 it rebuilds
the integer weights, checks every edge inequality and the negative total; it checks the two identities of
the uniform families for 3 <= m <= 1000, the forced-endpoint identity on a second grid, and the cells
(7, 9, 4), (8, 7, 2) and (19, 12, 3). Standard library only; a few seconds. With --json PATH the summary is
also written as JSON.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
import json
import sys


@dataclass(frozen=True)
class Obstruction:
    m: int
    d: int
    l: int
    j: int
    J: int
    a: int
    b: int
    c: int
    t: int
    rho: int
    F: int


def abs_sum(d: int, l: int, t: int) -> int:
    """Sum of |p - t| for p = d, ..., d + l - 1."""
    last = d + l - 1
    if t < d:
        return l * (2 * d + l - 1 - 2 * t) // 2
    if t > last:
        return l * (2 * t - 2 * d - l + 1) // 2
    u, v = t - d, last - t
    return (u * (u + 1) + v * (v + 1)) // 2


def family_half_cost(m: int, d: int, l: int, t: int) -> int:
    """H(t) = m S(t) - r(t - r)."""
    if min(m, d, l, t) < 1:
        raise ValueError("All parameters must be positive.")
    r = (m * l) % t
    return m * abs_sum(d, l, t) - r * (t - r)


def quadratic(m: int, d: int, l: int, j: int) -> Obstruction:
    if min(m, d, l, j) < 1:
        raise ValueError("All parameters must be positive.")
    J = j * (j + 1)
    a = m + J
    b = m * ((2 * j + 2) * l + 2 * d - 1)
    c = m * m * l * l + m * d * d + m * (l - 1) * d + m * l * (l - 1) // 2
    t = (b + a) // (2 * a)  # the nearest integer to b/(2a), ties upward
    rho = b - 2 * a * t
    F = a * t * t - b * t + c
    return Obstruction(m, d, l, j, J, a, b, c, t, rho, F)


def obstruction(m: int, d: int, l: int) -> str | Obstruction | None:
    """The finite test: the counting bound, then F_j(t_j) for the indices within the cutoff."""
    if min(m, d, l) < 1:
        raise ValueError("All parameters must be positive.")
    if 2 * d + l > 2 * m * l + 1:
        return "counting"
    j = 1
    while j <= m * l:
        J = j * (j + 1)
        if l >= 2 and J * (l * l - 1) >= m * l * l:
            break
        q = quadratic(m, d, l, j)
        if q.F < 0:
            return q
        j += 1
    return None


def check_explicit_certificate(q: Obstruction) -> None:
    """Rebuild the integer weights of the certificate at t_j and check every edge inequality and the total."""
    m, d, l, t = q.m, q.d, q.l, q.t
    if q.F >= 0 or t < 1:
        raise ValueError("A negative obstruction is required.")
    N = 2 * m * l
    actual_j = m * l // t
    sign = 1 if actual_j % 2 else -1

    def y(x: int) -> int:
        u = (2 * x - N - 1) % (4 * t)
        return sign * (t - min(u, 4 * t - u))

    for p in range(d, d + l):
        z = 2 * abs(p - t)
        for x in range(1, N - p + 1):
            assert y(x) + y(x + p) + z >= 0
    total = sum(y(x) for x in range(1, N + 1)) + 2 * m * abs_sum(d, l, t)
    assert total == 2 * family_half_cost(m, d, l, t)
    assert total <= 2 * q.F < 0


def main() -> None:
    cells = negatives = rounding_improvements = certificates = 0
    examples = []
    beyond_J_lt_m = []
    for m in range(1, 21):
        for l in range(1, 21):
            for d in range(1, ((2 * m - 1) * l + 1) // 2 + 3):  # two cells past the counting line
                cells += 1
                n = m * l
                full_min = min(family_half_cost(m, d, l, t) for t in range(1, max(n, d + l - 1) + 1))
                out = obstruction(m, d, l)
                assert (out is not None) == (full_min < 0), (m, d, l, out, full_min)
                if not isinstance(out, Obstruction):
                    continue
                negatives += 1
                q = out
                assert -q.a <= q.rho < q.a
                assert 4 * q.a * q.F == 4 * q.a * q.c - q.b * q.b + q.rho * q.rho
                x = 2 * q.J * d - ((2 * q.j + 1) * m - q.J) * l - q.J
                D = (m * m - q.J * q.J) * l * l + q.J * (m + q.J)
                assert q.J * (4 * q.a * q.c - q.b * q.b) == m * (x * x - D)
                if l >= 2:
                    assert q.J * (l * l - 1) < m * l * l
                    assert d <= q.t <= d + l - 1  # observed, not needed for soundness
                    assert q.j * q.t <= n <= (q.j + 1) * q.t
                old_worst = 4 * q.a * q.c - q.b * q.b + q.a * q.a
                if old_worst >= 0:
                    rounding_improvements += 1
                    if len(examples) < 10:
                        examples.append(asdict(q))
                if l >= 2 and q.J >= m and len(beyond_J_lt_m) < 10:
                    beyond_J_lt_m.append(asdict(q))
                if m <= 10 and l <= 8:
                    check_explicit_certificate(q)
                    certificates += 1
    # the two uniform families and the forced-endpoint identity
    for m in range(3, 1001):
        d, l, t = 3 * m - 3, 3, 3 * m - 2
        q = quadratic(m, d, l, 1)
        assert q.a * t * t - q.b * t + q.c == -4 * (m - 2)
        assert 2 * d + l <= 2 * m * l + 1
        assert m % 2 == 0 or l * (2 * d + l + 1) % 4 == 0
        d, l, t = 2 * m - 1, 2, 2 * m - 1
        q = quadratic(m, d, l, 1)
        assert q.a * t * t - q.b * t + q.c == 2 - m
    for m in range(1, 31):
        for l in range(1, 31):
            for d in range(1, m * l + 1):
                n = m * l
                q = quadratic(m, d, l, 1)
                e = 2 * n - 2 * d - l + 1
                endpoint = 4 * d * d - 6 * n * d + 2 * n * n + n * (l - 1)
                assert endpoint == 2 * (q.a * d * d - q.b * d + q.c)
                assert endpoint == (l - 1 + e) ** 2 - n * e
    examples_of_interest = []
    for m, d, l, j in [(7, 9, 4, 2), (8, 7, 2, 2), (19, 12, 3, 4)]:
        q = quadratic(m, d, l, j)
        check_explicit_certificate(q)
        assert q.F < 0
        assert m % 2 == 0 or l * (2 * d + l + 1) % 4 == 0
        examples_of_interest.append(asdict(q))
    rows = {}
    for m, l in [(3, 8), (3, 12), (3, 24), (4, 20), (16, 2)]:
        rows[f"m={m},l={l}"] = [d for d in range(1, ((2 * m - 1) * l + 1) // 2 + 1) if obstruction(m, d, l) is not None]
    result = {"grid": "1<=m<=20, 1<=l<=20, 1<=d<=floor(((2m-1)l+1)/2)+2",
              "cells": cells, "quadratic_obstructions": negatives,
              "explicit_edge_certificates_checked": certificates,
              "strict_improvements_over_worst_case_rounding": rounding_improvements,
              "rounding_examples": examples, "J_ge_m_examples_order_at_least_two": beyond_J_lt_m,
              "parity_admissible_examples_of_interest": examples_of_interest,
              "selected_rows": rows}
    args = sys.argv[1:]
    if "--json" in args:
        path = args[args.index("--json") + 1]
        with open(path, "w", encoding="utf-8") as f:
            json.dump(result, f, indent=2)
            f.write("\n")
    print(f"grid {result['grid']}: {cells} triples; the finite test agrees with the direct scan on every one; "
          f"{negatives} in-bound triples rejected; {certificates} certificates rebuilt and checked edge by edge; "
          f"{rounding_improvements} first-detected obstructions missed by the worst-case rounding test")
    print("selected rows:", "; ".join(f"({k}) d in [{v[0]}, {v[-1]}]" if v and v == list(range(v[0], v[-1] + 1))
                                     else f"({k}) {v}" for k, v in rows.items()))
    print("ALL EXACT-ARITHMETIC CHECKS PASSED")


if __name__ == "__main__":
    main()
