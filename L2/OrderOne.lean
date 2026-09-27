import L2.Necessity
import L2.Tight
import L2.Bridge
import L2.SixThree

/-!
# The row of order one, and the negative theorem

With one difference `d`, the positions `1, …, 2m` split into blocks of length `d` that alternate
between left ends and right ends, so `2d` divides `2m`; conversely `m / d` copies of the tight
cell `(d, 1)` at multiplicity `d`, side by side, form an `m`-fold sequence. Hence an `m`-fold
Langford sequence of order `1` and defect `d` exists exactly when `d ∣ m`. For `m ≥ 3` this gives
cells that satisfy the necessary conditions and admit no sequence: `(m − 1, 1)` for even `m`,
`(m − 2, 1)` for odd `m ≥ 5`, and `(6, 3)` for `m = 3`.
-/

namespace L2

/-- Necessity on the row of order one: the blocks `[1, d], [d + 1, 2d], …` alternate left ends and
right ends, so `2m` is a multiple of `2d`. -/
theorem dvd_of_order_one (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (s : ℕ → ℕ)
    (hs : Langford.IsLangford m d 1 s) : d ∣ m := by
  sorry

/-- Sufficiency on the row of order one: `m / d` juxtaposed copies of the tight cell `(d, 1)` at
multiplicity `d`. -/
theorem order_one_of_dvd (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (h : d ∣ m) :
    ∃ s : ℕ → ℕ, Langford.IsLangford m d 1 s := by
  sorry

/-- An `m`-fold Langford sequence of order `1` and defect `d` exists if and only if `d ∣ m`. -/
theorem order_one_iff_internal (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    (∃ s : ℕ → ℕ, Langford.IsLangford m d 1 s) ↔ d ∣ m :=
  ⟨fun ⟨s, hs⟩ => dvd_of_order_one m d hm hd s hs, order_one_of_dvd m d hm hd⟩

/-- For every `m ≥ 3` the necessary conditions are not sufficient. -/
theorem not_sufficient_internal (m : ℕ) (hm : 3 ≤ m) :
    ∃ d l : ℕ, 1 ≤ d ∧ 1 ≤ l ∧ 2 * d + l ≤ 2 * m * l + 1 ∧
      (m % 2 = 1 → l * (2 * d + l + 1) % 4 = 0) ∧ ¬ ∃ s : ℕ → ℕ, Langford.IsLangford m d l s := by
  sorry

end L2
