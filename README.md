# Two-fold Langford sequences exist exactly when 3l ≥ 2d − 1

A two-fold Langford sequence of order `l` and defect `d` is a sequence of `4l` positive integers in which every
`p` in `[d, d + l − 1]` fills the endpoints of two disjoint pairs of positions at distance `p`. The `m`-fold
version has `2ml` positions and `m` pairs for every `p`; `m = 1` gives ordinary Langford sequences.

Alkasasbeh, Dyer and Howell define two-fold Langford sequences in Section 2 of *Graceful labellings of variable
windmills using Skolem sequences*, [arXiv:2112.04265](https://arxiv.org/abs/2112.04265) (2021; journal version
*Graceful Labellings of Variable Windmills Using Skolem-type Sequences*, Ars Combinatoria 159 (2024) 109–131,
doi:10.61091/ars159-11), and in Section 7 ask for necessary and sufficient conditions for `m`-fold Langford
sequences with `m ≥ 2`. This repository answers that question for `m = 2` and proves, for `d, l ≥ 1` (all names
in the namespace `Langford`):

- a two-fold sequence exists if and only if `3l ≥ 2d − 1` — `twoFold_exists_iff`;
- every `m`-fold sequence satisfies the counting bound `(2m − 1)l ≥ 2d − 1`, and for odd `m` also
  `l(2d + l + 1) ≡ 0 (mod 4)` — `necessary`;
- the bound is attained: if `2d + l = 2ml + 1`, an `m`-fold sequence exists — `tight_exists`;
- an `m`-fold sequence of order `1` and defect `d` exists if and only if `d ∣ m` — `order_one_iff`;
- no three-fold sequence of order `3` and defect `6` exists — `not_threeFold_six_three`;
- for every `m ≥ 3` the conditions of `necessary` are not sufficient — `not_sufficient`;
- the residue bound: for every `T ≥ 1`, with `r = ml mod T`, `r(T − r) ≤ m·Σ_{p=d}^{d+l−1}|p − T|`; it contains
  the counting bound and the necessity half of the order-one theorem — `residue_bound`;
- the forced-endpoint bound: `6mld + ml ≤ 4d² + 2(ml)² + ml²`, that is `ml·e ≤ (l − 1 + e)²` for the excess
  `e = (2m − 1)l − 2d + 1` — `forced_endpoint`;
- order three: for every `m ≥ 3` the cell `(d, l) = (3m − 3, 3)` meets the conditions of `necessary` and has no
  `m`-fold sequence — `not_order_three`;
- rigidity: an `m`-fold sequence has `2d + l = 2ml + 1` exactly when every pair straddles the middle, that is
  `ml < i + s_i` for every position `i ≤ ml` — `tight_iff_straddle`.

The pairs are a chosen partition of the occurrences of `p`, so four copies of `p` at `a, a + p, a + 2p, a + 3p`
are allowed; this is the reading of Baker, Nowakowski, Shalaby and Sharary, whom the source cites for `m`-fold
sequences (the note's remark on chains gives the evidence).

Necessity is a distance sum: the left and right ends of the `ml` pairs split `{1, …, 2ml}`, their sums differ by
`m` times the sum of the differences, and that gap is at most `(ml)²`; the parity of the total gives the odd-`m`
condition. Sufficiency at `m = 2` is strong induction on `l`. The sixteen cells with `l ≤ 4` are literal; a cell
with `l ≥ 2d` is a concatenation of two smaller cells; every other cell comes, by Lemma S, from a permutation of
`{1, …, l}` whose shifted displacements and their mirrors fill `{1 − l, …, l}` (the signed-permutation problem).
That problem is solved on its whole range by inversion, the reversal, a descent along each line of fixed
`μ = 2(d − l) − 1`, and, in the band `l/2 < μ ≤ l`, by 21 block-reversal families plus the two-block reversal
`τ_l`, eight sporadic cells and three bases; each family is proved for all its parameters by a class table. The
tight line is `m` interleaved copies of the source's Table 1; the row `l = 1` alternates blocks of left and right
ends; the cell `(6, 3)` falls to a sum argument, and with the row `l = 1` it gives `not_sufficient`. The residue
bound sums a potential over the pairs: a triangle wave `V` on the positions with antiperiod `T` sums to
`±2r(T − r)` over `1, …, 2ml`, and each pair `{a, a + p}` has `|V(a) + V(a + p)| ≤ 2|p − T|`. The
forced-endpoint bound caps the sum of the left ends, which the distance sum fixes: the positions `1, …, d` are
left ends and no left end exceeds `2ml − d`; at `(3m − 3, 3)` it reads `12m ≤ 36`. `L2/Pairs.lean` adapts code
from the gn-lean development (PALOMAR-2026-09-07-000013; MIT; the same author).

Not claimed: no complete existence characterization for `m ≥ 3` (the formalized sufficient families are the
tight line and the row `l = 1`; the note adds, on paper, every cell with `3l ≥ 2d − 1` for even `m`, from the
two-fold theorem and juxtaposition); no count or closed form for the number of sequences; the linear-relaxation results
of the note in `note/` are not formalized, and the quadratic-family theorems of the note (§ on the
linear-programming picture) are paper-only.

> As of 2026-09-27, no characterization of two-fold or m-fold Langford sequences with d ≥ 2 was located in
> Alkasasbeh–Dyer–Howell (arXiv:2112.04265; Ars Combin. 159 (2024), which pose the question), Alkasasbeh's 2021 thesis
> and seven other Memorial University theses, Nordh's papers of 2005–2017, the Francetić–Mendelsohn survey and the
> Handbook of Combinatorial Designs (both by full-text index search), the signed-Langford and distance-labelling
> papers of 2016–2026, arXiv, Crossref, zbMATH, OpenAlex, the Internet Archive, OEIS, the formal-conjectures
> repository, or the Palomar registry.

Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`) are pinned by
the committed manifest; there are no GitHub Actions workflows.

```sh
lake exe cache get
lake build
python scripts/check-source.py
python scripts/check_langford.py
python scripts/check_bounds.py
python scripts/check_family.py
```

[PROOF.md](PROOF.md) gives the mathematics with the Lean name of every step, [VERIFICATION.md](VERIFICATION.md)
the checks and their limits, and [DISCLOSURE.md](DISCLOSURE.md) the assistance statement.
[Challenge.lean](Challenge.lean) states the ten theorems; [Solution.lean](Solution.lean) proves them.
[note/](note/README.md) holds the research note (CC BY-SA 4.0) and its finite-data certificate.

License: [MIT](LICENSE).
