# The proof

The mathematics of the development, with the Lean name carrying each step, in the order a reader
follows the Lean. The compared statements are in the namespace `Langford`; everything else is in
`L2`, in the modules under `L2/`.

## The definition and its reading

`Langford.IsLangford m d l s` (pinned in `Challenge.lean`, copied verbatim into `L2/Defs.lean`)
reads `s` on the positions `1, …, 2ml` and ignores its other values. Every entry lies in
`[d, d + l − 1]`, and for every `p` in that interval there is a set `A` of `m` left ends with
`1 ≤ a`, `a + p ≤ 2ml` and `a + p ∉ A`, such that the positions carrying `p` are exactly `A` and
`A + p`. This is the sequence form of Alkasasbeh, Dyer and Howell (Section 2) for general `m`, with
the pairs written out.

- The pairs are a chosen partition of the occurrences of `p`: four copies at `a, a + p, a + 2p,
  a + 3p` are two pairs. This is the `m`-fold reading of Baker, Nowakowski, Shalaby and Sharary,
  which the source follows. Under a reading that forbade such chains, the in-bound cells
  `(d, l) = (1, 1)`, `(5, 4)` and `(6, 6)` would have no sequence.
- Intervals are written as bounds, not as interval constants.
- `1 ≤ d` and `1 ≤ l` are hypotheses: for `l = 0` the empty sequence qualifies, and the source's
  parameters are positive.

A cell `(d, l)` is *in-bound* when `2d ≤ 3l + 1`, that is `3l ≥ 2d − 1`.

## Necessity and parity (`L2/Necessity.lean`)

`Nec.exists_choice` picks the left-end sets `A p` of a sequence (`Nec.Choice`). The left ends
`Nec.leftEnds` and right ends `Nec.rightEnds` are disjoint (`Nec.left_right_disjoint`), cover
`[1, 2ml]` (`Nec.left_right_union`) and have `ml` elements each (`Nec.card_left`, `Nec.card_right`).
Each pair adds its difference, so `ΣR = ΣL + m · Σ_{p=d}^{d+l−1} p` (`Nec.sum_right_sub_left`), and
`2 · Σ p = l(2d + l − 1)` (`Nec.sum_Icc_d`). A set of `ml` elements of `[1, 2ml]` has sum at most
that of the top `ml` (`Nec.sum_le_top`) and at least that of `[1, ml]` (`Nec.bottom_le_sum`), so
`ΣR − ΣL ≤ (ml)²`, which gives `ml(2d + l − 1) ≤ 2(ml)²` and, cancelling `ml`,
`2d + l ≤ 2ml + 1`. Since `ΣR + ΣL = ml(2ml + 1)`, the parity of `4ΣR` gives
`l(2d + l + 1) ≡ 0 (mod 4)` for odd `m`. Both are `necessary_internal`.

## Certificates and the bridge (`L2/Pairs.lean`, `L2/Multi.lean`, `L2/Bridge.lean`)

The constructions produce sets of pairs of integer positions. `pairEndpoints`, `pairDifferences`,
`shiftPairs` and the oriented endpoints `orientedPairs`, `orientedEndpoint` are in `L2/Pairs.lean`,
adapted from the gn-lean development (PALOMAR-2026-09-07-000013; MIT; the same author).

A `MultiPairing m d l C` is `m` colour classes of pairs whose difference sets are each
`[d, d + l − 1]`, whose endpoints together are `[1, 2ml]`, with at most `ml` pairs in all.
`TwoFold d l A B` is the two-colour case, and `TwoFold.toMulti` converts it. Two operations
build certificates: `TwoFold.concat` places `(d, l₁)` and `(d + l₁, l₂)`, shifted by `4l₁`, side by
side to give `(d, l₁ + l₂)`; `MultiPairing.juxtapose` places an `m₁`-fold and an `m₂`-fold
certificate of the same order and defect side by side.

The multiplicity bookkeeping is done once. A certificate has exactly `ml` pairs
(`MultiPairing.card_allPairs`), every position is exactly one oriented end
(`MultiPairing.endpoint_bijOn`), every colour has `l` pairs (`MultiPairing.card_colour`), colours
are disjoint (`MultiPairing.pairwise_disjoint`), differences within a colour are distinct
(`MultiPairing.diff_injOn`), so each `p` is carried by exactly `m` pairs (`MultiPairing.card_fiber`).
Reading at each position the difference of its pair (`toSeq`) gives a sequence, and
`MultiPairing.isLangford` proves it satisfies `Langford.IsLangford`.

## Lemma S (`L2/LemmaS.lean`)

`SP l δ G` (the signed-permutation problem, `L2/SP.lean`) says that `G` is the graph of a
permutation `σ` of `[1, l]` whose values `y_w = σ(w) − w + δ` (`val`) and mirrors `1 − y_w` (`mir`)
together are exactly `[1 − l, l]`. With `μ = 2δ − 1` this is `{|2(σ(w) − w) + μ|} = {1, 3, …, 2l − 1}`.

Lemma S, `SP.toTwoFold`: a solution gives a two-fold certificate of order `l` and defect `d = l + δ`.
The first colour (`colourA`) has the outer pairs `(l + 1 − w, 2l + y_w)`, the second (`colourB`) the
inner pairs `(2l + 1 − y_w, 3l + w)`. Both have differences `l + σ(w) + δ − 1`, which run over
`[d, d + l − 1]`; the outer ends fill `[1, l]` and `[3l + 1, 4l]`, and the middle ends `2l + y_w`
and `2l + 1 − y_w` fill `[l + 1, 3l]` because the values and mirrors tile `[1 − l, l]`
(`mem_pairEndpoints_colourA`, `mem_pairEndpoints_colourB`). The sequence is mirror-symmetric. The
cell `(d, l)` is in-bound exactly when `μ ≤ l`, and unsplittable (`l ≤ 2d − 1`) exactly when
`−l ≤ μ`.

## The signed-permutation problem on the cone (`L2/Rows.lean`, `L2/SP.lean`, `L2/Cone.lean`)

A *row* `row a c n` reverses the sources `[a + 1, a + n]` onto the targets `[c + 1, c + n]`. Along a
row the values and the mirrors are step-two runs (`mem_image_val_row`, `mem_image_mir_row`), and the
sources and targets are intervals (`mem_image_fst_row`, `mem_image_snd_row`).

- Inversion, `SP.inv`: the inverse permutation solves `SP(l, 1 − δ)`, so `μ ↦ −μ`.
- The reversal, `SP.reversal`: `w ↦ l + 1 − w` solves `SP(l, 1)`, the line `μ = 1`.
- The two-block reversal, `SP.tau`: for odd `l`, `τ_l` (`tauGraph`) reverses `[1, (l + 1)/2]` and
  `[(l + 3)/2, l]` and solves `SP(l, (l + 1)/2)`, the cell `μ = l`.
- Lemma C with inversion, `SP.cinv` (from `SP.cinv_aux`): from `SP(n, δ)` with `δ ≥ 1`, shift the
  targets by `μ`, place `τ_μ` on the new sources `[n + 1, n + μ]` with targets `[1, μ]`, which solves
  `SP(n + μ, 1 − δ)`, and invert (`cinvGraph`). This steps from order `n` to `n + μ` at the same `μ`;
  `SP.descend` iterates it.

Theorem R, `cone_sp`: `SP(l, δ)` has a solution for every `l ≥ 5` and `−l ≤ μ ≤ l`. By inversion
take `μ ≥ 1` (`cone_sp_pos`, induction on a bound for `l`). If `μ = 1`, the reversal; if `μ = l`,
`τ_l`; if `l < 2μ`, the band below. Otherwise `l' = l − μ ≥ μ`, and `SP.cinv` applies to a solution
at `(l', μ)`: `τ_μ` when `l' = μ`, the band when `μ < l' < 2μ` and `l' ≥ 5`, the induction when
`l' ≥ 2μ`. The one remaining case is `(l', μ) = (4, 3)`, where `SP(4, 2)` has no solution; there
`l = 7`, and `sp_7_3` is given directly. `SP(4, −1)` is empty as well, which is one reason the cells
with `l ≤ 4` are literal.

## The band by residue class (`L2/FamR0a.lean` to `L2/FamR3.lean`, `L2/Literals.lean`, `L2/Band.lean`)

The band is `l/2 < μ ≤ l`, `μ` odd, `l ≥ 5`. Each family `fam<Name>` is a union of rows whose starts
and sizes are affine in the parameters, listed in source order. Its theorem `fam<Name>_sp` proves
`SP(l, δ)` on the whole domain, stated as linear hypotheses in the parameters. The proof is a class
table: the sources and the targets tile `[1, l]`, and the value runs and mirror runs of the rows,
taken in two chains by parity, tile `[1 − l, l]`. The note gives every class table in full.

| Family | Parameters | `l` | `μ` | Blocks | Domain (parameters) | Domain in `(l, μ)` |
| --- | --- | --- | --- | --- | --- | --- |
| A1 | `q s` | `4q` | `4s + 1` | 9 | `q ≤ 2s`, `4s + 3 ≤ 3q` | `(l + 2)/2 ≤ μ ≤ (3l − 8)/4` |
| A3 | `q s` | `4q` | `4s + 3` | 9 | `q ≤ 2s + 1`, `4s + 5 ≤ 3q` | `(l + 2)/2 ≤ μ ≤ (3l − 8)/4` |
| U1 | `q s` | `4q` | `8s + 1` | 8 | `q + 1 ≤ 3s`, `2s + 1 ≤ q` | `(2l + 11)/3 ≤ μ ≤ l − 3` |
| U3 | `q s` | `4q` | `8s + 3` | 9 | `q ≤ 3s + 1`, `2s + 2 ≤ q`, `s + 4 ≤ q` | `(2l + 1)/3 ≤ μ ≤ l − 3`, `l ≥ 20` |
| U5 | `q s` | `4q` | `8s + 5` | 8 | `q ≤ 3s + 1`, `2s + 2 ≤ q` | `(2l + 7)/3 ≤ μ ≤ l − 3` |
| U7 | `q s` | `4q` | `8s + 7` | 9 | `2q ≤ 5s + 3`, `2s + 2 ≤ q` | `(4l + 11)/5 ≤ μ ≤ l − 1` |
| V | `q s` | `4q` | `4s + 3` | 9 | `2q ≤ 3s`, `5s + 3 ≤ 4q` | `(2l + 9)/3 ≤ μ ≤ (4l + 3)/5` |
| T | `q s` | `4q` | `8s + 3` | 7 | `4q ≤ 9s + 2`, `2s + 1 ≤ q` | `(8l + 11)/9 ≤ μ ≤ l − 1` |
| FA1 | `q s` | `4q + 1` | `4s + 1` | 8 | `q + 1 ≤ 2s`, `s + 1 ≤ q` | `(l + 5)/2 ≤ μ ≤ l − 4` |
| FA3 | `q s` | `4q + 1` | `4s + 3` | 7 | `q ≤ 2s`, `s + 2 ≤ q` | `(l + 5)/2 ≤ μ ≤ l − 6` |
| FT | `q` | `4q + 1` | `l − 2` | 6 | `2 ≤ q` | `l ≥ 9` |
| FL1 | `p` | `8p + 1` | `(l + 1)/2` | 7 | `2 ≤ p` | `l ≥ 17` |
| FL5 | `p` | `8p + 5` | `(l + 1)/2` | 6 | `1 ≤ p` | `l ≥ 13` |
| FA | `q h` | `4q + 2` | `2h − 1` | 5 | `q + 2 ≤ h`, `2h ≤ 3q + 2` | `(l + 4)/2 ≤ μ ≤ (3l − 2)/4` |
| FB2 | `k h` | `8k + 2` | `2h − 1` | 5 | `3k + 2 ≤ h ≤ 4k + 1` | `(3l + 6)/4 ≤ μ ≤ l − 1` |
| FB6 | `k h` | `8k + 6` | `2h − 1` | 5 | `3k + 4 ≤ h ≤ 4k + 3` | `(3l + 10)/4 ≤ μ ≤ l − 1` |
| F4 | `k` | `8k + 6` | `6k + 5` | 4 | `0 ≤ k` | `μ = (3l + 2)/4` |
| R3O | `q u` | `4q + 3` | `l − 4u − 2` | 7 | `1 ≤ u`, `2u + 1 ≤ q` | `(l + 3)/2 ≤ μ ≤ l − 6` |
| R3E | `q u` | `4q + 3` | `l − 4u` | 8 | `1 ≤ u`, `2u + 1 ≤ q` | `(l + 7)/2 ≤ μ ≤ l − 4` |
| R3Q | `q u` | `4q + 3` | `l − 4u` | 7 | `q + 1 ≤ 3u`, `2u ≤ q` | `(l + 3)/2 ≤ μ ≤ (2l − 1)/3` |
| R3T1 | `q` | `4q + 3` | `l − 2` | 6 | `1 ≤ q` | `l ≥ 7` |

In every row `δ = (μ + 1)/2`, and the `(l, μ)` domain is read inside the family's residue classes of
`l` and `μ`. The parameter domain above is the minimal form of the hypotheses of `fam<Name>_sp`,
which state the domain as the full list of block-size and type conditions. Besides the 21 families,
`τ_l` covers `μ = l` for odd `l`. The eleven literal solutions in `L2/Literals.lean` are the eight
sporadic cells `(l, μ) = (8, 5), (8, 7), (12, 9), (12, 11), (16, 11), (20, 15), (24, 17), (32, 23)`
and the three bases `(7, 3)`, `(5, 3)`, `(9, 5)` (`sp_8_5`, …, `sp_32_23`, `sp_7_3`, `sp_5_3`,
`sp_9_5`).

Coverage: `cover_r0`, `cover_r1`, `cover_r2`, `cover_r3` state, for each residue of `l` modulo `4`,
that every band cell lies in a family domain, is a literal cell, or has `μ = l`; `band_r0` to
`band_r3` assemble the solutions; `band_sp` is the band theorem. For `l ≡ 0` the cells outside
every family domain are exactly the eight sporadic cells; for `l ≡ 1` they are the bases `(5, 3)`
and `(9, 5)` and the cells `μ = l`; for `l ≡ 3`, the cells `μ = l`; `l ≡ 2` needs nothing more,
since `μ = l` is even there.

## The induction at m = 2 (`L2/Main.lean`)

`twoFold_all` proves a two-colour certificate at every in-bound cell by strong induction on `l`.

- `l ≤ 4`: the sixteen in-bound cells are literal, `twoFold_lit_d_l` in `L2/Literals.lean`.
- `l ≥ 5` and `l ≥ 2d`: with `l₁ = ⌊(2d + 1)/3⌋`, the cells `(d, l₁)` and `(d + l₁, l − l₁)` are
  in-bound and smaller, and `TwoFold.concat` joins them.
- `l ≥ 5` and `l ≤ 2d − 1`: `δ = d − l` gives `−l ≤ μ ≤ l`, so `cone_sp` and `SP.toTwoFold` apply.

`twoFold_exists_iff_internal` combines this with the bridge and with `necessary_internal` at `m = 2`
(which reads `2d + l ≤ 4l + 1`).

## The tight line (`L2/Tight.lean`)

`table1 d₀` is Table 1 of the source as pairs: `(d₀ − r, 2d₀ + r)` for `0 ≤ r ≤ d₀ − 1` and
`(2d₀ − 1 − r, 3d₀ + r)` for `0 ≤ r ≤ d₀ − 2`, an ordinary Langford sequence of defect `d₀` and
order `l = 2d₀ − 1` whose pairs all straddle the middle. Colour `c` of `tightColour m d₀` shifts its
left ends by `cl` and its right ends by `(m − 1 + c)l`; the blocks `[cl + 1, (c + 1)l]` cover
`[1, ml]` (`exists_block`). `tight_multi` proves the `m` colours a certificate of defect
`m(2d₀ − 1) − (d₀ − 1)`, which is the tight case `2d + l = 2ml + 1`; `tight_exists_internal` solves
for `d₀` and applies the bridge.

## The row l = 1 (`L2/OrderOne.lean`)

With one difference `d`, the positions `1, …, 2m` fall into blocks of length `d` that alternate
between left ends and right ends, so `2d ∣ 2m` (`dvd_of_order_one`). Conversely, `tight_multi` at
`d₀ = 1` is a `d`-fold certificate of order `1` and defect `d`, and `m / d` copies joined by
`MultiPairing.juxtapose` give an `m`-fold one (`order_one_of_dvd`). Together: `order_one_iff_internal`.

## The cell (6, 3) (`L2/SixThree.lean`)

A three-fold sequence of order `3` and defect `6` would fill `1, …, 18` with three pairs of each
difference `6, 7, 8`. Positions `1, …, 6` are left ends and `13, …, 18` right ends. The distance sum
gives `ΣL = 54`, so the three other left ends, in `7, …, 12`, sum to `33` and are `10, 11, 12`;
they pair with `18, 17, 16` in turn, all at distance `6`. Position `7` is a right end, and its partner in `[1, 6]` is at
distance `6` too, a fourth pair of difference `6`. This is `not_threeFold_six_three_internal`; the
cell meets both necessary conditions.

## The negative theorem (`L2/OrderOne.lean`)

`not_sufficient_internal`: for `m = 3` the cell `(6, 3)`; for even `m ≥ 4` the cell `(m − 1, 1)`;
for odd `m ≥ 5` the cell `(m − 2, 1)`. Each meets the necessary conditions, and the last two have no
sequence because `d ∤ m`.

## References

- A. H. Alkasasbeh, D. Dyer, J. Howell, *Graceful labellings of variable windmills using Skolem
  sequences*, arXiv:2112.04265 (2021); *Graceful Labellings of Variable Windmills Using Skolem-type
  Sequences*, Ars Combinatoria 159 (2024) 109–131, doi:10.61091/ars159-11.
- C. A. Baker, R. J. Nowakowski, N. Shalaby, A. Sharary, *m-fold and extended m-fold Skolem
  sequences*, Utilitas Math. 45 (1994) 153–167, Zbl 0808.05001.
- G. Nordh, *Perfect Skolem sets*, Discrete Math. 308 (2008) 1653–1664,
  doi:10.1016/j.disc.2006.12.003; its Theorem 15 (arXiv:math/0506155 v1 numbering) is the tight-line
  bijection in multiset form.
- J. E. Simpson, *Langford sequences: perfect and hooked*, Discrete Math. 44 (1983) 97–104,
  doi:10.1016/0012-365X(83)90008-0; `necessary` at `m = 1` matches its characterization.
- Th. Skolem, *On certain distributions of integers in pairs with given differences*, Math. Scand. 5
  (1957) 57–68, doi:10.7146/math.scand.a-10490.
- E. S. O'Keefe, *Verification of a conjecture of Th. Skolem*, Math. Scand. 9 (1961) 80–82,
  doi:10.7146/math.scand.a-10624.
- N. Francetić, E. Mendelsohn, *A survey of Skolem-type sequences and Rosa's use of them*, Math.
  Slovaca 59 (2009) 39–76, doi:10.2478/s12175-008-0110-3.
- gn-lean, PALOMAR-2026-09-07-000013, the source of `L2/Pairs.lean`.
