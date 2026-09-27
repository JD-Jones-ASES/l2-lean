import L2.Necessity

/-!
# The cell `(6, 3)` of the three-fold sequences

A three-fold Langford sequence of order `3` and defect `6` would occupy the positions `1, …, 18`
with three pairs of each difference `6`, `7`, `8`. Positions `1, …, 6` must be left ends and
`13, …, 18` right ends; the distance sum forces the three remaining left ends among `7, …, 12` to
sum to `33`, hence to be `10, 11, 12`, which are then the left ends of three pairs of difference
`6`. But position `7` is a right end, and its partner in `[1, 6]` forces a fourth pair of
difference `6`.
-/

namespace L2

/-- No three-fold Langford sequence of order `3` and defect `6` exists. -/
theorem not_threeFold_six_three_internal : ¬ ∃ s : ℕ → ℕ, Langford.IsLangford 3 6 3 s := by
  sorry

end L2
