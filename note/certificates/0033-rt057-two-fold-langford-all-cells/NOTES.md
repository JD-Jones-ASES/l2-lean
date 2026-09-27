# Certificate — a two-fold Langford sequence at every in-bound cell, built from the closed forms

**Statement.** A *two-fold Langford sequence of order l and defect d* is a partition of `[1, 4l]` into `2l` pairs
`{a, b}` in which each difference `b − a` in `[d, d + l − 1]` occurs exactly twice (Alkasasbeh, Dyer and Howell, Ars
Combin. 159 (2024), §2, in the pair-partition reading; chains `a, a+p, a+2p, a+3p` allowed). Certified here: **for every
`1 ≤ l ≤ L` and every `1 ≤ d ≤ ⌊(3l+1)/2⌋` — that is, every cell with `3l ≥ 2d − 1` — an explicit sequence exists**, and
it is produced by the proof's own constructions: concatenation for splittable cells; for the rest, Lemma S applied to a
signed permutation obtained by the reversal, `τ_l`, the descent along fixed `μ` (Lemma C with inversion), or one of the
21 band families (FA, FB2, FB6, F4; A1, A3, U1, U3, U5, U7, V, T; FA3, FA1, FT, FL1, FL5; R3O, R3E, R3Q, R3T1) with the
explicit bases `(7, 3)`, `(5, 3)`, `(9, 5)` and the eight sporadic cells `(l, μ) = (8, 5), (8, 7), (12, 9), (12, 11),
(16, 11), (20, 15), (24, 17), (32, 23)`. The only literal two-fold witnesses are cells with `l ≤ 4` (`verify.py`: two,
at `(d, l) = (3, 4)` and `(6, 4)`, where the signed-permutation problem is empty; `verify_second.py`: the sixteen cells
with `l ≤ 4`). The counting bound is the converse (necessity), proved in the note and not re-derived here. Also checked:
the `m`-fold tight line, `m` copies of the paper's Table 1 bijection, for `1 ≤ m ≤ 6` and odd `l ≤ 41` (126 cells).

**Method.** Each script rebuilds every cell by the route above and checks the result with its own exact checker (the
positions partition `[1, 4l]`; the difference multiset is exactly `2 × [d, d + l − 1]`); `verify.py` also checks each
signed permutation in displacement form (Lemma P) before lifting, runs a census over every family's whole domain with
negative controls (63 mutants rejected), and re-finds the eight sporadic permutations by its own exact search;
`verify_second.py` checks the domain of every family to `l ≤ 160`, cross-checks its closed-form `k`-step descent against
the iterated form on 2,701 chains, and rejects 16 mutated witnesses. Route counts at `L = 300` (`verify.py`): 25,331
concatenations, 600 reversals, 150 `τ_l`, 19,665 band-family cells, 22,052 descent chains, 2 literals.

**Artifacts and replay.** `verify.py` and `verify_second.py` are standalone, standard-library Python 3 (≥ 3.9), with the
family tables inline. From this folder:

```sh
python verify.py 300 --no-routes      # 13 s; exit 0; last line "VERDICT: ALL VERIFIED ..."
python verify_second.py 300           # 15 s; exit 0; last line "VERDICT: PASS ..."
```

Both are unchanged under `python -O` (no `assert` carries a check). `verify.py` was run to `L = 1000` (751,000 cells)
and `verify_second.py` to `L = 600`; `run_300.log` and `run_second_300.log` are their logs at `L = 300` from this folder. Without `--no-routes`, `verify.py`
writes `routes_<L>.json` (the route of every cell) beside itself. An optional file `KILL` in this folder stops a long run.

**Label.** CHECKED to `L = 1000` (one implementation) and to `L = 600` (a second, independent implementation); every
family's class table is proved in the note and formalized in the Lean development, and the reduction chain is proved
there too — so the certificate is the finite witness of a theorem, not the theorem's proof.

**External dependency ledger.** None in the trust chain: no solver, no data file, no import beyond the standard library
(the 2 or 16 literal cells are inline and re-checked at start-up; `verify_second.py` cross-reads a witness file when one
is present beside it, as a logged consistency line only — absent the file, nothing changes). The family tables are
transcribed from the class tables; the checker does not trust them: every cell is checked from the definition.

**Implication.** For `l ≤ L`, every in-bound cell has a checked sequence. For all `l` the run is evidence only; the
theorem follows from the class-table proofs, Theorem R and the concatenation induction, which the Lean development
in `L2/` proves.

**Independent verification.** Two implementations written independently, sharing no code; their route counts agree
cell class by cell class at `L = 300` (concatenation 25,331 vs 25,326 with 16 literals, band 19,665 vs 19,667, descent
22,052 vs 22,050 — the differences are the literal-versus-construction choice at `l ≤ 4` and the `(7, 3)` routing).
