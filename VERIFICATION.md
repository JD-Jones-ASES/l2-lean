# Verification

All six statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard
and the standard-library cross-check pass.

## Formal scope

| Statement | Proved in |
| --- | --- |
| `Langford.twoFold_exists_iff` — a two-fold sequence exists iff `3l ≥ 2d − 1` | L2/Main.lean |
| `Langford.necessary` — `(2m − 1)l ≥ 2d − 1`, and the parity condition for odd `m` | L2/Necessity.lean |
| `Langford.tight_exists` — a sequence on the line `2d + l = 2ml + 1` | L2/Tight.lean, L2/Main.lean |
| `Langford.order_one_iff` — order `1`: a sequence exists iff `d ∣ m` | L2/OrderOne.lean |
| `Langford.not_threeFold_six_three` — no three-fold sequence at `(d, l) = (6, 3)` | L2/SixThree.lean |
| `Langford.not_sufficient` — for `m ≥ 3` the necessary conditions are not sufficient | L2/OrderOne.lean |

Each is restated verbatim in Solution.lean and closed by the internal theorem of the same name with
the suffix `_internal`. The layers behind them: pairs and certificates in L2/Pairs.lean,
L2/Multi.lean and L2/Bridge.lean; the signed-permutation problem in L2/Rows.lean and L2/SP.lean;
Lemma S in L2/LemmaS.lean; the 21 block-reversal families in L2/FamR0a.lean, L2/FamR0b.lean,
L2/FamR1.lean, L2/FamR2.lean and L2/FamR3.lean; the literals in L2/Literals.lean; the band and the
cone in L2/Band.lean and L2/Cone.lean. PROOF.md names the lemma behind each step.

## Local checks

```sh
lake exe cache get
lake build
python scripts/check-source.py
python scripts/check_langford.py
```

The `Test` target audits every constant whose name begins with `L2.`, `Langford.`, `_private.L2.` or
`_private.Solution.` (DESK_FILLS at the time of writing, floor 600), permits only `propext`,
`Classical.choice` and `Quot.sound`, and fails if any of the six compared theorems is missing. A
placeholder in a proof compiles with a warning; this audit is what fails the build. Challenge.lean
intentionally contains six proof placeholders; Solution.lean and the modules it imports contain
none, and Solution.lean does not import Challenge.lean. The source guard rejects `sorry`, `admit`,
`axiom`, `unsafe`, `partial`, `native_decide`, `implemented_by`, `extern`, `Lean.ofReduceBool` and
the kernel-bypass options in `L2/`, Solution.lean and `Test/`, the same tokens except `sorry` in
Challenge.lean, and any `debug.` option in the `[leanOptions]` table of lakefile.toml.

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) are
pinned by the committed manifest; `lake update` is never run. A clean build takes DESK_FILLS.

## The finite computations

There is no `native_decide`. The only kernel computations are the twenty-seven literal
certificates of L2/Literals.lean, each a few equalities of literal finite sets of integer pairs,
evaluated by `decide`; there is no search inside any proof.

| Computation | Size |
| --- | --- |
| The sixteen two-fold certificates `twoFold_lit_d_l`, every in-bound cell with `l ≤ 4` | two colours of `l` pairs each, at most 16 positions; DESK_FILLS |
| The eleven `SP` solutions `sp_5_3`, `sp_7_3`, `sp_8_5`, `sp_8_7`, `sp_9_5`, `sp_12_9`, `sp_12_11`, `sp_16_11`, `sp_20_15`, `sp_24_17` | permutations of 5 to 24 points; DESK_FILLS |
| `sp_32_23`, by `decide +kernel` | a permutation of 32 points; DESK_FILLS |

The family theorems are linear arithmetic over `ℤ` (`omega`), split by the sign and parity of the
value as the class tables direct. The heaviest family theorems and their build times:
DESK_FILLS.

Mutation controls: DESK_FILLS.

`scripts/check_langford.py` recomputes the finite content with the standard library and exact
integers, independently of Lean: the sixteen literal certificates and the eleven `SP` solutions
from the definitions; all 21 families at every domain cell with `l ≤ 120` (1,901 cells), each
checked as a solution of `SP` and lifted through Lemma S to a two-fold sequence; the reversal,
`τ_l`, and the band coverage to `l = 120`; the cone to `l = 60` and the induction of L2/Main.lean to
`l = 40`; an exhaustive search for `l ≤ 5`; the tight line for `m ≤ 6` and odd `l ≤ 21`; the row
`l = 1` for `m ≤ 12` against `d ∣ m`; the cell `(6, 3)` at `m = 3` by exhaustive search (212 nodes);
and two controls. The family tables in the script are transcribed from the Lean definitions. It
runs in a few seconds and ends:

```text
ok    control: A1 at (4, 2) with the target starts of its first two blocks exchanged does not solve SP, as it must not
ok    control: the lift of sp_7_3 with the right ends of two pairs exchanged is not a two-fold sequence of order 7 and defect 9, as it must not be

ALL CHECKS PASSED
```

The research note in `note/` carries its own finite-data certificate, which rebuilds a two-fold
sequence at every in-bound cell to `l = 300` by two independent implementations; see
[note/README.md](note/README.md).

## Not checked here

- Sufficiency for `m ≥ 3`: only the negative theorem and the two positive families (the tight line
  and the row `l = 1`) are proved; the note's linear-relaxation results and its conjecture for
  `m ≥ 3` are not formalized.
- Counting: no number of sequences and no closed form is claimed.
- The source's constructions are not formalized; its Table 1 is used as data for the tight line.
- The literal certificates and the families are witnesses, not claimed to be canonical.
- The Python script and the note's certificate are cross-checks of finite instances, not premises
  of any Lean proof.
