import L2.Main

/-!
# The compared theorems

The six theorems of `Challenge.lean`, restated character for character and proved from the
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

end Langford
