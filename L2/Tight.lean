import L2.Multi

/-!
# The tight line for every multiplicity

For `l = 2d₀ − 1` the ordinary Langford sequence of defect `d₀` and order `l` whose pairs all
straddle the middle (Table 1 of the source) has its left ends on `[1, l]` and its right ends on
`[l + 1, 2l]`. Taking `m` copies, the `c`-th with left ends shifted by `cl` and right ends by
`(m − 1 + c)l`, gives an `m`-fold Langford sequence of order `l` and defect
`d = m(2d₀ − 1) − (d₀ − 1)`, which is the tight case `2d + l = 2ml + 1`.
-/

namespace L2
noncomputable section

/-- Table 1 as pairs: `(d₀ − r, 2d₀ + r)` for `0 ≤ r ≤ d₀ − 1` and `(2d₀ − 1 − r, 3d₀ + r)` for
`0 ≤ r ≤ d₀ − 2`; an ordinary Langford sequence of defect `d₀` and order `2d₀ − 1`, all pairs
straddling the middle. -/
def table1 (d₀ : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc 0 (d₀ - 1)).image (fun r => (d₀ - r, 2 * d₀ + r)) ∪
    (Finset.Icc 0 (d₀ - 2)).image (fun r => (2 * d₀ - 1 - r, 3 * d₀ + r))

/-- Colour `c` of the `m`-fold tight sequence of order `l = 2d₀ − 1`: copy `c` of Table 1 with left
ends shifted by `c·l` and right ends by `(m − 1 + c)·l`. -/
def tightColour (m : ℕ) (d₀ : ℤ) (c : ℕ) : Finset (ℤ × ℤ) :=
  (table1 d₀).image fun q => (q.1 + c * (2 * d₀ - 1), q.2 + (m - 1 + c) * (2 * d₀ - 1))

/-- The blocks `[cl + 1, cl + l]`, `c < m`, cover `[1, ml]`. -/
theorem exists_block (m : ℕ) (l x : ℤ) (hl : 1 ≤ l) (h1 : 1 ≤ x) (h2 : x ≤ m * l) :
    ∃ c < m, (c : ℤ) * l + 1 ≤ x ∧ x ≤ (c : ℤ) * l + l := by
  sorry

/-- The tight line: `m` interleaved copies of Table 1 form an `m`-fold Langford sequence of order
`2d₀ − 1` and defect `m(2d₀ − 1) − (d₀ − 1)`. -/
theorem tight_multi (m : ℕ) (d₀ : ℤ) (hm : 1 ≤ m) (hd : 1 ≤ d₀) :
    MultiPairing m (m * (2 * d₀ - 1) - (d₀ - 1)) (2 * d₀ - 1) (tightColour m d₀) := by
  sorry

end
end L2
