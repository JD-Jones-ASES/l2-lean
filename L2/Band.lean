import L2.FamR0a
import L2.FamR0b
import L2.FamR1
import L2.FamR2
import L2.FamR3
import L2.Literals

/-!
# The band

Every cell `l/2 < μ ≤ l`, `μ` odd, `l ≥ 5`, of the signed-permutation problem has a solution
(`δ = (μ + 1)/2`). By residue class of `l` modulo `4`, each such cell lies in the domain of one of
the block-reversal families, is one of the explicit cells, or has `μ = l` (the two-block reversal
`τ_l`). The coverage lemmas state the case split; the band lemmas assemble the solutions.
-/

namespace L2

/-- Every band cell with `l ≡ 0 (mod 4)` lies in the domain of one of the families, or is one of the explicit cells. -/
theorem cover_r0 (l μ : ℤ) (h4 : l % 4 = 0) (hl : 8 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ) (hhi : μ < l) :
    (∃ q s : ℤ, l = 4 * q ∧ μ = 4 * s + 1 ∧ q ≤ 2 * s ∧ q ≤ 2 * s + 1 ∧ 1 ≤ s ∧ s + 1 ≤ q ∧ s + 1 ≤ q ∧ 2 ≤ q ∧ 1 ≤ q ∧ 1 ≤ q ∧ s + 1 ≤ 2 * q ∧ s + 1 ≤ 2 * q ∧ s ≤ 2 * q ∧ 4 * s + 3 ≤ 3 * q) ∨  -- A1
    (∃ q s : ℤ, l = 4 * q ∧ μ = 4 * s + 3 ∧ q ≤ 2 * s + 1 ∧ q ≤ 2 * s + 2 ∧ 1 ≤ s ∧ 0 ≤ s ∧ s + 2 ≤ q ∧ s + 1 ≤ q ∧ 2 ≤ q ∧ 1 ≤ q ∧ 1 ≤ q ∧ s + 2 ≤ 2 * q ∧ s + 1 ≤ 2 * q ∧ s + 1 ≤ 2 * q ∧ 4 * s + 5 ≤ 3 * q) ∨  -- A3
    (∃ q s : ℤ, l = 4 * q ∧ μ = 8 * s + 1 ∧ q + 1 ≤ 3 * s ∧ 1 ≤ s ∧ 0 ≤ s ∧ 0 ≤ s ∧ 2 * s + 1 ≤ q ∧ s + 2 ≤ q ∧ s + 1 ≤ q ∧ s + 1 ≤ q ∧ s + 1 ≤ q ∧ s ≤ q ∧ s ≤ q ∧ 0 ≤ q + s) ∨  -- U1
    (∃ q s : ℤ, l = 4 * q ∧ μ = 8 * s + 3 ∧ q ≤ 3 * s + 1 ∧ 1 ≤ s ∧ 0 ≤ s ∧ 0 ≤ s ∧ 2 * s + 2 ≤ q ∧ s + 4 ≤ q ∧ s + 2 ≤ q ∧ s + 2 ≤ q ∧ s + 1 ≤ q ∧ s + 1 ≤ q ∧ s ≤ q ∧ 0 ≤ q + s) ∨  -- U3
    (∃ q s : ℤ, l = 4 * q ∧ μ = 8 * s + 5 ∧ q ≤ 3 * s + 1 ∧ 0 ≤ s ∧ 0 ≤ s ∧ 0 ≤ s ∧ 2 * s + 2 ≤ q ∧ s + 2 ≤ q ∧ s + 1 ≤ q ∧ s + 1 ≤ q ∧ s + 1 ≤ q ∧ s ≤ q ∧ 0 ≤ q + s + 1) ∨  -- U5
    (∃ q s : ℤ, l = 4 * q ∧ μ = 8 * s + 7 ∧ 2 * q ≤ 5 * s + 3 ∧ 2 * q ≤ 5 * s + 4 ∧ 0 ≤ s ∧ 0 ≤ s + 1 ∧ 2 * s + 2 ≤ q ∧ 2 * s + 2 ≤ q ∧ s + 2 ≤ q ∧ s + 1 ≤ q ∧ 3 * s + 3 ≤ 2 * q ∧ s + 1 ≤ 2 * q) ∨  -- U7
    (∃ q s : ℤ, l = 4 * q ∧ μ = 4 * s + 3 ∧ 3 * q ≤ 5 * s + 1 ∧ 2 * q ≤ 3 * s ∧ 2 * q ≤ 3 * s ∧ 2 * q ≤ 3 * s + 1 ∧ q ≤ 2 * s ∧ q ≤ 2 * s + 1 ∧ 1 ≤ s ∧ 0 ≤ s ∧ 0 ≤ s ∧ s + 2 ≤ q ∧ s + 1 ≤ q ∧ s + 1 ≤ q ∧ 0 ≤ q ∧ s + 1 ≤ 2 * q ∧ s ≤ 2 * q ∧ s + 1 ≤ q ∧ 5 * s + 3 ≤ 4 * q) ∨  -- V
    (∃ q s : ℤ, l = 4 * q ∧ μ = 8 * s + 3 ∧ 4 * q ≤ 9 * s + 2 ∧ 2 * q ≤ 5 * s + 2 ∧ 1 ≤ s ∧ 0 ≤ s ∧ 2 * s + 1 ≤ q ∧ 2 * s + 1 ≤ q ∧ s + 1 ≤ q ∧ 3 * s + 2 ≤ 2 * q ∧ 3 * s + 1 ≤ 2 * q ∧ 3 * s + 1 ≤ 2 * q ∧ s ≤ 2 * q ∧ 7 * s + 3 ≤ 4 * q) ∨  -- T
    (l = 8 ∧ μ = 5) ∨
    (l = 8 ∧ μ = 7) ∨
    (l = 12 ∧ μ = 9) ∨
    (l = 12 ∧ μ = 11) ∨
    (l = 16 ∧ μ = 11) ∨
    (l = 20 ∧ μ = 15) ∨
    (l = 24 ∧ μ = 17) ∨
    (l = 32 ∧ μ = 23) := by
  sorry

/-- Every band cell with `l ≡ 1 (mod 4)` lies in the domain of one of the families, or is one of the explicit cells, or has `μ = l`. -/
theorem cover_r1 (l μ : ℤ) (h4 : l % 4 = 1) (hl : 5 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ) (hhi : μ ≤ l) :
    (∃ q s : ℤ, l = 4 * q + 1 ∧ μ = 4 * s + 1 ∧ q + 1 ≤ 2 * s ∧ s + 1 ≤ q) ∨  -- FA1
    (∃ q s : ℤ, l = 4 * q + 1 ∧ μ = 4 * s + 3 ∧ q ≤ 2 * s ∧ s + 2 ≤ q) ∨  -- FA3
    (∃ q : ℤ, l = 4 * q + 1 ∧ μ = 4 * q - 1 ∧ 2 ≤ q) ∨  -- FT
    (∃ p : ℤ, l = 8 * p + 1 ∧ μ = 4 * p + 1 ∧ 2 ≤ p) ∨  -- FL1
    (∃ p : ℤ, l = 8 * p + 5 ∧ μ = 4 * p + 3 ∧ 1 ≤ p) ∨  -- FL5
    (l = 5 ∧ μ = 3) ∨
    (l = 9 ∧ μ = 5) ∨
    μ = l := by  -- τ_l
  sorry

/-- Every band cell with `l ≡ 2 (mod 4)` lies in the domain of one of the families. -/
theorem cover_r2 (l μ : ℤ) (h4 : l % 4 = 2) (hl : 6 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ) (hhi : μ < l) :
    (∃ q h : ℤ, l = 4 * q + 2 ∧ μ = 2 * h - 1 ∧ q + 2 ≤ h ∧ 2 * h ≤ 3 * q + 2) ∨  -- FA
    (∃ k h : ℤ, l = 8 * k + 2 ∧ μ = 2 * h - 1 ∧ 1 ≤ k ∧ 3 * k + 2 ≤ h ∧ h ≤ 4 * k + 1) ∨  -- FB2
    (∃ k h : ℤ, l = 8 * k + 6 ∧ μ = 2 * h - 1 ∧ 3 * k + 4 ≤ h ∧ h ≤ 4 * k + 3) ∨  -- FB6
    (∃ k : ℤ, l = 8 * k + 6 ∧ μ = 6 * k + 5 ∧ 0 ≤ k) := by  -- F4
  sorry

/-- Every band cell with `l ≡ 3 (mod 4)` lies in the domain of one of the families, or has `μ = l`. -/
theorem cover_r3 (l μ : ℤ) (h4 : l % 4 = 3) (hl : 7 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ) (hhi : μ ≤ l) :
    (∃ q : ℤ, l = 4 * q + 3 ∧ μ = 4 * q + 1 ∧ 1 ≤ q) ∨  -- R3T1
    (∃ q u : ℤ, l = 4 * q + 3 ∧ μ = 4 * q + 1 - 4 * u ∧ 1 ≤ u ∧ 2 * u + 1 ≤ q) ∨  -- R3O
    (∃ q u : ℤ, l = 4 * q + 3 ∧ μ = 4 * q + 3 - 4 * u ∧ 1 ≤ u ∧ 2 * u + 1 ≤ q) ∨  -- R3E
    (∃ q u : ℤ, l = 4 * q + 3 ∧ μ = 4 * q + 3 - 4 * u ∧ q + 1 ≤ 3 * u ∧ 2 * u ≤ q) ∨  -- R3Q
    μ = l := by  -- τ_l
  sorry

/-- The band for `l ≡ 0 (mod 4)`. -/
theorem band_r0 (l μ : ℤ) (h4 : l % 4 = 0) (hl : 8 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ)
    (hhi : μ < l) : ∃ G, SP l ((μ + 1) / 2) G := by
  sorry

/-- The band for `l ≡ 1 (mod 4)`. -/
theorem band_r1 (l μ : ℤ) (h4 : l % 4 = 1) (hl : 5 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ)
    (hhi : μ ≤ l) : ∃ G, SP l ((μ + 1) / 2) G := by
  sorry

/-- The band for `l ≡ 2 (mod 4)`. -/
theorem band_r2 (l μ : ℤ) (h4 : l % 4 = 2) (hl : 6 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ)
    (hhi : μ < l) : ∃ G, SP l ((μ + 1) / 2) G := by
  sorry

/-- The band for `l ≡ 3 (mod 4)`. -/
theorem band_r3 (l μ : ℤ) (h4 : l % 4 = 3) (hl : 7 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ)
    (hhi : μ ≤ l) : ∃ G, SP l ((μ + 1) / 2) G := by
  sorry

/-- Every band cell `l/2 < μ ≤ l`, `μ` odd, `l ≥ 5`, has a solution. -/
theorem band_sp (l μ : ℤ) (hl : 5 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ) (hhi : μ ≤ l) :
    ∃ G, SP l ((μ + 1) / 2) G := by
  have h4 : l % 4 = 0 ∨ l % 4 = 1 ∨ l % 4 = 2 ∨ l % 4 = 3 := by omega
  rcases h4 with h4 | h4 | h4 | h4
  · exact band_r0 l μ h4 (by omega) hμ hlo (by omega)
  · exact band_r1 l μ h4 hl hμ hlo hhi
  · exact band_r2 l μ h4 (by omega) hμ hlo (by omega)
  · exact band_r3 l μ h4 (by omega) hμ hlo hhi

end L2
