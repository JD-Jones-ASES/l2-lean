import Mathlib

/-!
# Two-fold Langford sequences exist exactly when 3l ≥ 2d − 1

A two-fold Langford sequence of order `l` and defect `d` (Alkasasbeh, Dyer and Howell, *Graceful
labellings of variable windmills using Skolem sequences*, arXiv:2112.04265, Section 2) is a
sequence of `4l` positive integers in which every `p` in `[d, d + l − 1]` occupies two disjoint
pairs of positions at distance `p`. The `m`-fold version has `2ml` positions and `m` disjoint pairs
for every `p`; `m = 1` gives ordinary Langford sequences and `d = 1` gives `m`-fold Skolem
sequences. Section 7 of the paper asks for necessary and sufficient conditions for the existence
of `m`-fold Langford sequences with `m ≥ 2`.

`IsLangford m d l s` reads `s` on the positions `1, …, 2ml`; values elsewhere are ignored. For each
`p` the finite set `A` holds the left ends of the `m` pairs `{a, a + p}`; the clause `a + p ∉ A`
makes the pairs pairwise disjoint, and the last clause says that the positions carrying `p` are
exactly their endpoints. The pairs are a chosen partition of the occurrences of `p`, so four
occurrences at `a, a + p, a + 2p, a + 3p` are allowed (Baker, Nowakowski, Shalaby and Sharary's
reading of `m`-fold sequences, which the source follows). Intervals are written with bounds. The
hypotheses `1 ≤ d` and `1 ≤ l` are needed: for `l = 0` the empty sequence qualifies, and the
paper's parameters are positive.

This Mathlib-only file intentionally contains placeholders (six theorems from the first version of the
development and four added afterwards: the residue bound, the forced-endpoint bound, the order-three cells
and the rigidity of the counting bound). The corresponding Solution
declarations are proved in a separate environment.
-/

namespace Langford

/-- `s` is an `m`-fold Langford sequence of order `l` and defect `d`, read on the positions
`1, …, 2ml`: every entry lies in `[d, d + l − 1]`, and for every `p` in that interval the positions
carrying `p` are exactly the endpoints of `m` pairwise disjoint pairs `{a, a + p}`. -/
def IsLangford (m d l : ℕ) (s : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, 1 ≤ i → i ≤ 2 * m * l → d ≤ s i ∧ s i < d + l) ∧
  ∀ p : ℕ, d ≤ p → p < d + l →
    ∃ A : Finset ℕ, A.card = m ∧
      (∀ a ∈ A, 1 ≤ a ∧ a + p ≤ 2 * m * l ∧ a + p ∉ A) ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ 2 * m * l → (s i = p ↔ i ∈ A ∨ ∃ a ∈ A, i = a + p)

/-- For `d ≥ 1` and `l ≥ 1`, a two-fold Langford sequence of order `l` and defect `d` exists
if and only if `3l ≥ 2d − 1`. -/
theorem twoFold_exists_iff (d l : ℕ) (hd : 1 ≤ d) (hl : 1 ≤ l) :
    (∃ s : ℕ → ℕ, IsLangford 2 d l s) ↔ 2 * d ≤ 3 * l + 1 := by
  sorry

/-- Every `m`-fold Langford sequence (`m, d, l ≥ 1`) satisfies `(2m − 1)l ≥ 2d − 1`, and for odd
`m` also `l(2d + l + 1) ≡ 0 (mod 4)`, which for `m = 1` is the classical parity condition. -/
theorem necessary (m d l : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (s : ℕ → ℕ)
    (hs : IsLangford m d l s) :
    2 * d + l ≤ 2 * m * l + 1 ∧ (m % 2 = 1 → l * (2 * d + l + 1) % 4 = 0) := by
  sorry

/-- The bound is attained for every multiplicity: if `2d + l = 2ml + 1` (so `l` is odd), an
`m`-fold Langford sequence of order `l` and defect `d` exists. -/
theorem tight_exists (m d l : ℕ) (hm : 1 ≤ m) (h : 2 * d + l = 2 * m * l + 1) :
    ∃ s : ℕ → ℕ, IsLangford m d l s := by
  sorry

/-- The row of order one: an `m`-fold Langford sequence of order `1` and defect `d` exists if and
only if `d` divides `m`. -/
theorem order_one_iff (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    (∃ s : ℕ → ℕ, IsLangford m d 1 s) ↔ d ∣ m := by
  sorry

/-- No three-fold Langford sequence of order `3` and defect `6` exists, although
`2·6 + 3 ≤ 2·3·3 + 1` and `3·(2·6 + 3 + 1) ≡ 0 (mod 4)`. -/
theorem not_threeFold_six_three : ¬ ∃ s : ℕ → ℕ, IsLangford 3 6 3 s := by
  sorry

/-- For every `m ≥ 3` the necessary conditions of `necessary` are not sufficient: some
`(d, l)` with `d, l ≥ 1` satisfies them and admits no `m`-fold Langford sequence. -/
theorem not_sufficient (m : ℕ) (hm : 3 ≤ m) :
    ∃ d l : ℕ, 1 ≤ d ∧ 1 ≤ l ∧ 2 * d + l ≤ 2 * m * l + 1 ∧
      (m % 2 = 1 → l * (2 * d + l + 1) % 4 = 0) ∧ ¬ ∃ s : ℕ → ℕ, IsLangford m d l s := by
  sorry

/-- The residue bound. For every `T ≥ 1`, with `r = ml mod T`, an `m`-fold Langford sequence satisfies
`r(T − r) ≤ m · Σ_{p=d}^{d+l−1} |p − T|`; the distance `|p − T|` is written with truncated subtraction as
`(p − T) + (T − p)`, and `p = d + i`. For `T ≥ max(ml, d + l − 1)` this is the counting bound of `necessary`;
at `l = 1`, `T = d` it says `d ∣ m`. -/
theorem residue_bound (m d l T : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (hT : 1 ≤ T) (s : ℕ → ℕ)
    (hs : IsLangford m d l s) :
    (m * l % T) * (T - m * l % T) ≤ m * ∑ i ∈ Finset.range l, ((d + i - T) + (T - (d + i))) := by
  sorry

/-- The forced-endpoint bound `6mld + ml ≤ 4d² + 2(ml)² + ml²`, that is `ml · e ≤ (l − 1 + e)²` for the
excess `e = (2m − 1)l − 2d + 1`: the positions `1, …, d` are left ends, every left end is at most `2ml − d`,
and the distance sum fixes the sum of the left ends. -/
theorem forced_endpoint (m d l : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (s : ℕ → ℕ)
    (hs : IsLangford m d l s) :
    6 * m * l * d + m * l ≤ 4 * d * d + 2 * (m * l) * (m * l) + m * l * l := by
  sorry

/-- One order-three cell for every multiplicity: for every `m ≥ 3` the cell `(d, l) = (3m − 3, 3)` satisfies
the conditions of `necessary` and admits no `m`-fold Langford sequence. -/
theorem not_order_three (m : ℕ) (hm : 3 ≤ m) :
    2 * (3 * m - 3) + 3 ≤ 2 * m * 3 + 1 ∧ (m % 2 = 1 → 3 * (2 * (3 * m - 3) + 3 + 1) % 4 = 0) ∧
      ¬ ∃ s : ℕ → ℕ, IsLangford m (3 * m - 3) 3 s := by
  sorry

/-- Equality in the counting bound is rigid: an `m`-fold Langford sequence has `2d + l = 2ml + 1` if and only
if every pair straddles the midpoint: every position `i ≤ ml` has `ml < i + s i`. -/
theorem tight_iff_straddle (m d l : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (s : ℕ → ℕ)
    (hs : IsLangford m d l s) :
    2 * d + l = 2 * m * l + 1 ↔ ∀ i : ℕ, 1 ≤ i → i ≤ m * l → m * l < i + s i := by
  sorry

end Langford
