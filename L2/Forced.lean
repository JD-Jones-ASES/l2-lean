import L2.Necessity
import L2.SixThree

/-!
# The forced-endpoint bound, the order-three cells and the top of order two

In an `m`-fold Langford sequence the positions `1, …, d` are left ends (a right end `a + p` has `a ≥ 1` and
`p ≥ d`) and every left end is at most `2ml − d`. So the left ends are `[1, d]` together with `ml − d` positions of
`[d + 1, 2ml − d]`, whose sum is at most that of the top `ml − d` of them; the distance sum fixes the sum of the
left ends, and comparing gives `6mld + ml ≤ 4d² + 2(ml)² + ml²`, that is `ml · e ≤ (l − 1 + e)²` for the excess
`e = (2m − 1)l − 2d + 1`. At `(d, l) = (3m − 3, 3)` the excess is `4` and the bound reads `12m ≤ 36`, so for `m ≥ 4`
the cell is empty although it satisfies the counting bound and the parity condition; `m = 3` is the cell `(6, 3)`.
At `(2m − 1, 2)`, the top of the order-two row, the bound reads `2m ≤ 4`.
-/

namespace L2

set_option linter.unusedVariables false in
/-- The forced-endpoint bound `6mld + ml ≤ 4d² + 2(ml)² + ml²`. -/
theorem forced_endpoint_internal (m d l : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (s : ℕ → ℕ)
    (hs : Langford.IsLangford m d l s) :
    6 * m * l * d + m * l ≤ 4 * d * d + 2 * (m * l) * (m * l) + m * l * l := by
  sorry

/-- One order-three cell for every multiplicity: for every `m ≥ 3` the cell `(3m − 3, 3)` satisfies the counting
bound and the parity condition and admits no `m`-fold Langford sequence. -/
theorem not_order_three_internal (m : ℕ) (hm : 3 ≤ m) :
    2 * (3 * m - 3) + 3 ≤ 2 * m * 3 + 1 ∧ (m % 2 = 1 → 3 * (2 * (3 * m - 3) + 3 + 1) % 4 = 0) ∧
      ¬ ∃ s : ℕ → ℕ, Langford.IsLangford m (3 * m - 3) 3 s := by
  sorry

/-- The top of the order-two row is empty for every `m ≥ 3`: no `m`-fold Langford sequence of order `2` and defect
`2m − 1` exists. For even `m` the cell satisfies the counting bound and the parity condition; for odd `m` the parity
condition already excludes it. -/
theorem not_order_two_top_internal (m : ℕ) (hm : 3 ≤ m) :
    ¬ ∃ s : ℕ → ℕ, Langford.IsLangford m (2 * m - 1) 2 s := by
  sorry

end L2
