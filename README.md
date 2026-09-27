# Two-fold Langford sequences exist exactly when 3l ≥ 2d − 1

A two-fold Langford sequence of order `l` and defect `d` is a sequence of `4l` positive integers in
which every `p` in `[d, d + l − 1]` fills the endpoints of two disjoint pairs of positions at
distance `p`. The `m`-fold version has `2ml` positions and `m` pairs for every `p`; `m = 1` gives
ordinary Langford sequences.

Alkasasbeh, Dyer and Howell define two-fold Langford sequences in Section 2 of *Graceful labellings of variable
windmills using Skolem sequences*, [arXiv:2112.04265](https://arxiv.org/abs/2112.04265) (2021;
journal version *Graceful Labellings of Variable Windmills Using Skolem-type Sequences*, Ars
Combinatoria 159 (2024) 109–131, doi:10.61091/ars159-11), and in Section 7 ask for necessary and
sufficient conditions for `m`-fold Langford sequences with `m ≥ 2`. This repository answers that
question for `m = 2` and proves, for `d, l ≥ 1` (all names in the namespace `Langford`):

- a two-fold sequence exists if and only if `3l ≥ 2d − 1` — `twoFold_exists_iff`;
- every `m`-fold sequence satisfies `(2m − 1)l ≥ 2d − 1`, and for odd `m` also
  `l(2d + l + 1) ≡ 0 (mod 4)` — `necessary`;
- the bound is attained: if `2d + l = 2ml + 1`, an `m`-fold sequence exists — `tight_exists`;
- an `m`-fold sequence of order `1` and defect `d` exists if and only if `d ∣ m` — `order_one_iff`;
- no three-fold sequence of order `3` and defect `6` exists — `not_threeFold_six_three`;
- for every `m ≥ 3` the conditions of `necessary` are not sufficient — `not_sufficient`.

The pairs are a chosen partition of the occurrences of `p`, so four copies of `p` at
`a, a + p, a + 2p, a + 3p` are allowed; this is the reading of Baker, Nowakowski, Shalaby and
Sharary, whom the source cites for `m`-fold sequences (the note's remark on chains gives the
evidence).

Necessity is a distance sum: the left and right ends of the `ml` pairs split `{1, …, 2ml}`, their
sums differ by `m` times the sum of the differences, and that gap is at most `(ml)²`; the parity of
the total gives the odd-`m` condition. Sufficiency at `m = 2` is strong induction on `l`. The sixteen
cells with `l ≤ 4` are literal; a cell with `l ≥ 2d` is a concatenation of two smaller cells; every
other cell comes, by Lemma S, from a permutation of `{1, …, l}` whose shifted displacements and their
mirrors fill `{1 − l, …, l}` (the signed-permutation problem). That problem is solved on its whole
range by inversion, the reversal, a descent along each line of fixed `μ = 2(d − l) − 1`, and, in the
band `l/2 < μ ≤ l`, by 21 block-reversal families plus the two-block reversal `τ_l`, eight sporadic
cells and three bases; each family is proved for all its parameters by a class table. The tight line
is `m` interleaved copies of the source's Table 1; the row `l = 1` alternates blocks of left and right
ends; the cell `(6, 3)` falls to a sum argument, and with the row `l = 1` it gives `not_sufficient`.
`L2/Pairs.lean` adapts code from the gn-lean development (PALOMAR-2026-09-07-000013; MIT; the same
author).

Not claimed: no sufficient condition for `m ≥ 3` beyond the negative theorem; no count or closed
form for the number of sequences; the linear-relaxation results of the note in `note/` are not
formalized.

> As of 2026-09-27, no characterization of two-fold or m-fold Langford sequences with d ≥ 2 was located in
> Alkasasbeh–Dyer–Howell (arXiv:2112.04265; Ars Combin. 159 (2024), which pose the question), Alkasasbeh's 2021 thesis
> and seven other Memorial University theses, Nordh's papers of 2005–2017, the Francetić–Mendelsohn survey and the
> Handbook of Combinatorial Designs (both by full-text index search), the signed-Langford and distance-labelling
> papers of 2016–2026, arXiv, Crossref, zbMATH, OpenAlex, the Internet Archive, OEIS, the formal-conjectures
> repository, or the Palomar registry.

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) are
pinned by the committed manifest; there are no GitHub Actions workflows.

```sh
lake exe cache get
lake build
python scripts/check-source.py
python scripts/check_langford.py
```

[PROOF.md](PROOF.md) gives the mathematics with the Lean name of every step,
[VERIFICATION.md](VERIFICATION.md) the checks and their limits, and [DISCLOSURE.md](DISCLOSURE.md)
the assistance statement. [Challenge.lean](Challenge.lean) states the six theorems;
[Solution.lean](Solution.lean) proves them. [note/](note/README.md) holds the research note (CC BY-SA
4.0) and its finite-data certificate.

License: [MIT](LICENSE).
