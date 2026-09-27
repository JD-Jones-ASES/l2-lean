import L2.Main

/-!
# The compared theorems

The ten theorems of `Challenge.lean`, restated character for character and proved from the
development.
-/

namespace Langford

/-- For `d ≥ 1` and `l ≥ 1`, a two-fold Langford sequence of order `l` and defect `d` exists
if and only if `3l ≥ 2d − 1`. -/
theorem twoFold_exists_iff (d l : ℕ) (hd : 1 ≤ d) (hl : 1 ≤ l) :
    (∃ s : ℕ → ℕ, IsLangford 2 d l s) ↔ 2 * d ≤ 3 * l + 1 := by
  exact L2.twoFold_exists_iff_internal d l hd hl

/-- Every `m`-fold Langford sequence (`m, d, l ≥ 1`) satisfies `(2m − 1)l ≥ 2d − 1`, and for odd
`m` also `l(2d + l + 1) ≡ 0 (mod 4)`, which for `m = 1` is the classical parity condition. -/
theorem necessary (m d l : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (s : ℕ → ℕ)
    (hs : IsLangford m d l s) :
    2 * d + l ≤ 2 * m * l + 1 ∧ (m % 2 = 1 → l * (2 * d + l + 1) % 4 = 0) := by
  exact L2.necessary_internal m d l hm hd hl s hs

/-- The bound is attained for every multiplicity: if `2d + l = 2ml + 1` (so `l` is odd), an
`m`-fold Langford sequence of order `l` and defect `d` exists. -/
theorem tight_exists (m d l : ℕ) (hm : 1 ≤ m) (h : 2 * d + l = 2 * m * l + 1) :
    ∃ s : ℕ → ℕ, IsLangford m d l s := by
  exact L2.tight_exists_internal m d l hm h

/-- The row of order one: an `m`-fold Langford sequence of order `1` and defect `d` exists if and
only if `d` divides `m`. -/
theorem order_one_iff (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    (∃ s : ℕ → ℕ, IsLangford m d 1 s) ↔ d ∣ m := by
  exact L2.order_one_iff_internal m d hm hd

/-- No three-fold Langford sequence of order `3` and defect `6` exists, although
`2·6 + 3 ≤ 2·3·3 + 1` and `3·(2·6 + 3 + 1) ≡ 0 (mod 4)`. -/
theorem not_threeFold_six_three : ¬ ∃ s : ℕ → ℕ, IsLangford 3 6 3 s := by
  exact L2.not_threeFold_six_three_internal

/-- For every `m ≥ 3` the necessary conditions of `necessary` are not sufficient: some
`(d, l)` with `d, l ≥ 1` satisfies them and admits no `m`-fold Langford sequence. -/
theorem not_sufficient (m : ℕ) (hm : 3 ≤ m) :
    ∃ d l : ℕ, 1 ≤ d ∧ 1 ≤ l ∧ 2 * d + l ≤ 2 * m * l + 1 ∧
      (m % 2 = 1 → l * (2 * d + l + 1) % 4 = 0) ∧ ¬ ∃ s : ℕ → ℕ, IsLangford m d l s := by
  exact L2.not_sufficient_internal m hm

/-- The residue bound. For every `T ≥ 1`, with `r = ml mod T`, an `m`-fold Langford sequence satisfies
`r(T − r) ≤ m · Σ_{p=d}^{d+l−1} |p − T|`; the distance `|p − T|` is written with truncated subtraction as
`(p − T) + (T − p)`, and `p = d + i`. For `T ≥ max(ml, d + l − 1)` this is the counting bound of `necessary`;
at `l = 1`, `T = d` it says `d ∣ m`. -/
theorem residue_bound (m d l T : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (hT : 1 ≤ T) (s : ℕ → ℕ)
    (hs : IsLangford m d l s) :
    (m * l % T) * (T - m * l % T) ≤ m * ∑ i ∈ Finset.range l, ((d + i - T) + (T - (d + i))) := by
  exact L2.residue_bound_internal m d l T hm hd hl hT s hs

/-- The forced-endpoint bound `6mld + ml ≤ 4d² + 2(ml)² + ml²`, that is `ml · e ≤ (l − 1 + e)²` for the
excess `e = (2m − 1)l − 2d + 1`: the positions `1, …, d` are left ends, every left end is at most `2ml − d`,
and the distance sum fixes the sum of the left ends. -/
theorem forced_endpoint (m d l : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (s : ℕ → ℕ)
    (hs : IsLangford m d l s) :
    6 * m * l * d + m * l ≤ 4 * d * d + 2 * (m * l) * (m * l) + m * l * l := by
  exact L2.forced_endpoint_internal m d l hm hd hl s hs

/-- One order-three cell for every multiplicity: for every `m ≥ 3` the cell `(d, l) = (3m − 3, 3)` satisfies
the conditions of `necessary` and admits no `m`-fold Langford sequence. -/
theorem not_order_three (m : ℕ) (hm : 3 ≤ m) :
    2 * (3 * m - 3) + 3 ≤ 2 * m * 3 + 1 ∧ (m % 2 = 1 → 3 * (2 * (3 * m - 3) + 3 + 1) % 4 = 0) ∧
      ¬ ∃ s : ℕ → ℕ, IsLangford m (3 * m - 3) 3 s := by
  exact L2.not_order_three_internal m hm

/-- Equality in the counting bound is rigid: an `m`-fold Langford sequence has `2d + l = 2ml + 1` if and only
if every pair straddles the midpoint: every position `i ≤ ml` has `ml < i + s i`. -/
theorem tight_iff_straddle (m d l : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (s : ℕ → ℕ)
    (hs : IsLangford m d l s) :
    2 * d + l = 2 * m * l + 1 ↔ ∀ i : ℕ, 1 ≤ i → i ≤ m * l → m * l < i + s i := by
  exact L2.tight_iff_straddle_internal m d l hm hd hl s hs

end Langford
