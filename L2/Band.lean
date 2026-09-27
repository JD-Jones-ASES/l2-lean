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

/-- Every band cell with `l ≡ 0 (mod 4)` lies in the domain of one of the families, or is one of the explicit cells.
Write `l = 4q` and split on `μ mod 8`. In each residue class the domains of the families, read as intervals of `μ`
at fixed `q`, chain from `μ = l/2 + 1` up to `μ = l - 1` once `q ≥ 17`; for `2 ≤ q ≤ 16` the cells outside every
domain are exactly the eight explicit cells. -/
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
  obtain ⟨q, rfl⟩ : ∃ q, l = 4 * q := ⟨l / 4, by omega⟩
  have hq2 : 2 ≤ q := by omega
  have h8 : μ % 8 = 1 ∨ μ % 8 = 3 ∨ μ % 8 = 5 ∨ μ % 8 = 7 := by omega
  rcases h8 with h8 | h8 | h8 | h8
  · obtain ⟨t, rfl⟩ : ∃ t, μ = 8 * t + 1 := ⟨μ / 8, by omega⟩
    by_cases hA1 : 4 * (2 * t) + 3 ≤ 3 * q
    · exact Or.inl ⟨q, 2 * t, rfl, by ring, by omega⟩
    by_cases hU1 : q + 1 ≤ 3 * t
    · exact Or.inr (Or.inr (Or.inl ⟨q, t, rfl, by ring, by omega⟩))
    iterate 8 right
    clear h4 hμ h8
    have key : (q = 3 ∧ t = 1) ∨ (q = 6 ∧ t = 2) := by omega
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  · obtain ⟨t, rfl⟩ : ∃ t, μ = 8 * t + 3 := ⟨μ / 8, by omega⟩
    by_cases hA3 : (2 * t) + 2 ≤ q ∧ 4 * (2 * t) + 5 ≤ 3 * q
    · exact Or.inr (Or.inl ⟨q, 2 * t, rfl, by ring, by omega⟩)
    by_cases hU3 : q ≤ 3 * t + 1 ∧ 2 * t + 2 ≤ q ∧ t + 4 ≤ q
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, t, rfl, by ring, by omega⟩)))
    by_cases hV : 2 * q ≤ 3 * (2 * t) ∧ (2 * t) + 2 ≤ q ∧ 5 * (2 * t) + 3 ≤ 4 * q
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, 2 * t, rfl, by ring, by omega⟩))))))
    by_cases hT : 4 * q ≤ 9 * t + 2 ∧ 2 * q ≤ 5 * t + 2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, t, rfl, by ring, by omega⟩)))))))
    iterate 8 right
    clear h4 hμ h8
    have key : (q = 3 ∧ t = 1) ∨ (q = 4 ∧ t = 1) := by omega
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  · obtain ⟨t, rfl⟩ : ∃ t, μ = 8 * t + 5 := ⟨μ / 8, by omega⟩
    by_cases hA1 : 4 * (2 * t + 1) + 3 ≤ 3 * q
    · exact Or.inl ⟨q, 2 * t + 1, rfl, by ring, by omega⟩
    by_cases hU5 : q ≤ 3 * t + 1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, t, rfl, by ring, by omega⟩))))
    iterate 8 right
    clear h4 hμ h8
    have key : q = 2 ∧ t = 0 := by omega
    obtain ⟨rfl, rfl⟩ := key
    norm_num
  · obtain ⟨t, rfl⟩ : ∃ t, μ = 8 * t + 7 := ⟨μ / 8, by omega⟩
    by_cases hA3 : (2 * t + 1) + 2 ≤ q ∧ 4 * (2 * t + 1) + 5 ≤ 3 * q
    · exact Or.inr (Or.inl ⟨q, 2 * t + 1, rfl, by ring, by omega⟩)
    by_cases hU7 : 2 * q ≤ 5 * t + 3
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, t, rfl, by ring, by omega⟩)))))
    by_cases hV : 2 * q ≤ 3 * (2 * t + 1) ∧ (2 * t + 1) + 2 ≤ q ∧ 5 * (2 * t + 1) + 3 ≤ 4 * q
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, 2 * t + 1, rfl, by ring, by omega⟩))))))
    iterate 8 right
    clear h4 hμ h8
    have hq : q ≤ 16 := by omega
    have key : (q = 2 ∧ t = 0) ∨ (q = 5 ∧ t = 1) ∨ (q = 8 ∧ t = 2) := by
      interval_cases q <;> omega
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

/-- Every band cell with `l ≡ 1 (mod 4)` lies in the domain of one of the families, or is one of the explicit cells, or has `μ = l`.
Write `l = 4q + 1`. For `μ = 4s + 1 < l`: `FA1` when `q + 1 ≤ 2s`, else `q = 2s` (`FL1`, or the base `(9, 5)`). For
`μ = 4s + 3`: `FA3` when `s + 2 ≤ q ≤ 2s`; `μ = l − 2` is `FT` (or the base `(5, 3)`); else `q = 2s + 1` (`FL5`, or
the base `(5, 3)`). -/
theorem cover_r1 (l μ : ℤ) (h4 : l % 4 = 1) (hl : 5 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ) (hhi : μ ≤ l) :
    (∃ q s : ℤ, l = 4 * q + 1 ∧ μ = 4 * s + 1 ∧ q + 1 ≤ 2 * s ∧ s + 1 ≤ q) ∨  -- FA1
    (∃ q s : ℤ, l = 4 * q + 1 ∧ μ = 4 * s + 3 ∧ q ≤ 2 * s ∧ s + 2 ≤ q) ∨  -- FA3
    (∃ q : ℤ, l = 4 * q + 1 ∧ μ = 4 * q - 1 ∧ 2 ≤ q) ∨  -- FT
    (∃ p : ℤ, l = 8 * p + 1 ∧ μ = 4 * p + 1 ∧ 2 ≤ p) ∨  -- FL1
    (∃ p : ℤ, l = 8 * p + 5 ∧ μ = 4 * p + 3 ∧ 1 ≤ p) ∨  -- FL5
    (l = 5 ∧ μ = 3) ∨
    (l = 9 ∧ μ = 5) ∨
    μ = l := by  -- τ_l
  obtain ⟨q, rfl⟩ : ∃ q, l = 4 * q + 1 := ⟨l / 4, by omega⟩
  by_cases hτ : μ = 4 * q + 1
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hτ))))))
  have hm : μ % 4 = 1 ∨ μ % 4 = 3 := by omega
  rcases hm with hm | hm
  · obtain ⟨s, rfl⟩ : ∃ s, μ = 4 * s + 1 := ⟨μ / 4, by omega⟩
    by_cases hA : q + 1 ≤ 2 * s ∧ s + 1 ≤ q
    · exact Or.inl ⟨q, s, rfl, rfl, hA⟩
    by_cases hs : 2 ≤ s
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, by omega, rfl, hs⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
  · obtain ⟨s, rfl⟩ : ∃ s, μ = 4 * s + 3 := ⟨μ / 4, by omega⟩
    by_cases hA : q ≤ 2 * s ∧ s + 2 ≤ q
    · exact Or.inr (Or.inl ⟨q, s, rfl, rfl, hA⟩)
    by_cases hT : s + 1 = q
    · by_cases hq : 2 ≤ q
      · exact Or.inr (Or.inr (Or.inl ⟨q, rfl, by omega, hq⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
    · by_cases hs : 1 ≤ s
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, by omega, rfl, hs⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))

/-- Every band cell with `l ≡ 2 (mod 4)` lies in the domain of one of the families.
Write `l = 4q + 2` and `μ = 2h − 1`, so `q + 2 ≤ h ≤ 2q + 1`. `FA` covers `2h ≤ 3q + 2`; above it, `FB2` when
`q = 2k`, and `F4` (`h = 3k + 3`) or `FB6` when `q = 2k + 1`. -/
theorem cover_r2 (l μ : ℤ) (h4 : l % 4 = 2) (hl : 6 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ) (hhi : μ < l) :
    (∃ q h : ℤ, l = 4 * q + 2 ∧ μ = 2 * h - 1 ∧ q + 2 ≤ h ∧ 2 * h ≤ 3 * q + 2) ∨  -- FA
    (∃ k h : ℤ, l = 8 * k + 2 ∧ μ = 2 * h - 1 ∧ 1 ≤ k ∧ 3 * k + 2 ≤ h ∧ h ≤ 4 * k + 1) ∨  -- FB2
    (∃ k h : ℤ, l = 8 * k + 6 ∧ μ = 2 * h - 1 ∧ 3 * k + 4 ≤ h ∧ h ≤ 4 * k + 3) ∨  -- FB6
    (∃ k : ℤ, l = 8 * k + 6 ∧ μ = 6 * k + 5 ∧ 0 ≤ k) := by  -- F4
  obtain ⟨q, rfl⟩ : ∃ q, l = 4 * q + 2 := ⟨l / 4, by omega⟩
  obtain ⟨h, rfl⟩ : ∃ h, μ = 2 * h - 1 := ⟨(μ + 1) / 2, by omega⟩
  by_cases hA : 2 * h ≤ 3 * q + 2
  · exact Or.inl ⟨q, h, rfl, rfl, by omega, hA⟩
  have hq : q % 2 = 0 ∨ q % 2 = 1 := by omega
  rcases hq with hq | hq
  · obtain ⟨k, rfl⟩ : ∃ k, q = 2 * k := ⟨q / 2, by omega⟩
    exact Or.inr (Or.inl ⟨k, h, by ring, rfl, by omega, by omega, by omega⟩)
  · obtain ⟨k, rfl⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
    by_cases hF : h = 3 * k + 3
    · exact Or.inr (Or.inr (Or.inr ⟨k, by ring, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨k, h, by ring, rfl, by omega, by omega⟩))

/-- Every band cell with `l ≡ 3 (mod 4)` lies in the domain of one of the families, or has `μ = l`.
Write `l = 4q + 3`. For `μ = 4q + 1 − 4u`: `R3T1` at `u = 0`, else `R3O`. For `μ = 4q + 3 − 4u`: `τ_l` at `u = 0`,
`R3E` when `2u + 1 ≤ q`, else `q = 2u` and `R3Q`. -/
theorem cover_r3 (l μ : ℤ) (h4 : l % 4 = 3) (hl : 7 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ) (hhi : μ ≤ l) :
    (∃ q : ℤ, l = 4 * q + 3 ∧ μ = 4 * q + 1 ∧ 1 ≤ q) ∨  -- R3T1
    (∃ q u : ℤ, l = 4 * q + 3 ∧ μ = 4 * q + 1 - 4 * u ∧ 1 ≤ u ∧ 2 * u + 1 ≤ q) ∨  -- R3O
    (∃ q u : ℤ, l = 4 * q + 3 ∧ μ = 4 * q + 3 - 4 * u ∧ 1 ≤ u ∧ 2 * u + 1 ≤ q) ∨  -- R3E
    (∃ q u : ℤ, l = 4 * q + 3 ∧ μ = 4 * q + 3 - 4 * u ∧ q + 1 ≤ 3 * u ∧ 2 * u ≤ q) ∨  -- R3Q
    μ = l := by  -- τ_l
  obtain ⟨q, rfl⟩ : ∃ q, l = 4 * q + 3 := ⟨l / 4, by omega⟩
  have hm : μ % 4 = 1 ∨ μ % 4 = 3 := by omega
  rcases hm with hm | hm
  · obtain ⟨u, rfl⟩ : ∃ u, μ = 4 * q + 1 - 4 * u := ⟨(4 * q + 1 - μ) / 4, by omega⟩
    by_cases hu : u = 0
    · exact Or.inl ⟨q, rfl, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨q, u, rfl, rfl, by omega, by omega⟩)
  · obtain ⟨u, rfl⟩ : ∃ u, μ = 4 * q + 3 - 4 * u := ⟨(4 * q + 3 - μ) / 4, by omega⟩
    by_cases hu : u = 0
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
    by_cases hE : 2 * u + 1 ≤ q
    · exact Or.inr (Or.inr (Or.inl ⟨q, u, rfl, rfl, by omega, hE⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, u, rfl, rfl, by omega, by omega⟩)))

/-- A solution of `SP(l, δ)` solves the cell `μ` of order `l` whenever `(μ + 1)/2 = δ`. -/
theorem band_of {l μ δ : ℤ} {G : Finset (ℤ × ℤ)} (h : SP l δ G) (hδ : (μ + 1) / 2 = δ) :
    ∃ G, SP l ((μ + 1) / 2) G :=
  ⟨G, hδ ▸ h⟩

/-- The band for `l ≡ 0 (mod 4)`: each cell is solved by the family whose domain contains it (`A1`, `A3`, `U1`, `U3`,
`U5`, `U7`, `V`, `T`) or by one of the eight explicit solutions. -/
theorem band_r0 (l μ : ℤ) (h4 : l % 4 = 0) (hl : 8 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ)
    (hhi : μ < l) : ∃ G, SP l ((μ + 1) / 2) G := by
  rcases cover_r0 l μ h4 hl hμ hlo hhi with
    ⟨q, s, rfl, rfl, h⟩ | ⟨q, s, rfl, rfl, h⟩ | ⟨q, s, rfl, rfl, h⟩ | ⟨q, s, rfl, rfl, h⟩ |
    ⟨q, s, rfl, rfl, h⟩ | ⟨q, s, rfl, rfl, h⟩ | ⟨q, s, rfl, rfl, h⟩ | ⟨q, s, rfl, rfl, h⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hG : SP (4 * q) (2 * s + 1) (famA1 q s) := by apply famA1_sp <;> omega
    exact band_of hG (by omega)
  · have hG : SP (4 * q) (2 * s + 2) (famA3 q s) := by apply famA3_sp <;> omega
    exact band_of hG (by omega)
  · have hG : SP (4 * q) (4 * s + 1) (famU1 q s) := by apply famU1_sp <;> omega
    exact band_of hG (by omega)
  · have hG : SP (4 * q) (4 * s + 2) (famU3 q s) := by apply famU3_sp <;> omega
    exact band_of hG (by omega)
  · have hG : SP (4 * q) (4 * s + 3) (famU5 q s) := by apply famU5_sp <;> omega
    exact band_of hG (by omega)
  · have hG : SP (4 * q) (4 * s + 4) (famU7 q s) := by apply famU7_sp <;> omega
    exact band_of hG (by omega)
  · have hG : SP (4 * q) (2 * s + 2) (famV q s) := by apply famV_sp <;> omega
    exact band_of hG (by omega)
  · have hG : SP (4 * q) (4 * s + 2) (famT q s) := by apply famT_sp <;> omega
    exact band_of hG (by omega)
  · exact band_of sp_8_5 (by norm_num)
  · exact band_of sp_8_7 (by norm_num)
  · exact band_of sp_12_9 (by norm_num)
  · exact band_of sp_12_11 (by norm_num)
  · exact band_of sp_16_11 (by norm_num)
  · exact band_of sp_20_15 (by norm_num)
  · exact band_of sp_24_17 (by norm_num)
  · exact band_of sp_32_23 (by norm_num)

/-- The band for `l ≡ 1 (mod 4)`: the families `FA1`, `FA3`, `FT`, `FL1`, `FL5`, the explicit bases `(5, 3)` and
`(9, 5)`, and `τ_l` at `μ = l`. -/
theorem band_r1 (l μ : ℤ) (h4 : l % 4 = 1) (hl : 5 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ)
    (hhi : μ ≤ l) : ∃ G, SP l ((μ + 1) / 2) G := by
  rcases cover_r1 l μ h4 hl hμ hlo hhi with
    ⟨q, s, rfl, rfl, h1, h2⟩ | ⟨q, s, rfl, rfl, h1, h2⟩ | ⟨q, rfl, rfl, h1⟩ | ⟨p, rfl, rfl, h1⟩ |
    ⟨p, rfl, rfl, h1⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
  · exact band_of (famFA1_sp q s h1 h2) (by omega)
  · exact band_of (famFA3_sp q s h1 h2) (by omega)
  · exact band_of (famFT_sp q h1) (by omega)
  · exact band_of (famFL1_sp p h1) (by omega)
  · exact band_of (famFL5_sp p h1) (by omega)
  · exact band_of sp_5_3 (by norm_num)
  · exact band_of sp_9_5 (by norm_num)
  · exact ⟨_, SP.tau _ (by omega) hμ⟩

/-- The band for `l ≡ 2 (mod 4)`: the families `FA`, `FB2`, `FB6`, `F4` (`μ = l` is even here). -/
theorem band_r2 (l μ : ℤ) (h4 : l % 4 = 2) (hl : 6 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ)
    (hhi : μ < l) : ∃ G, SP l ((μ + 1) / 2) G := by
  rcases cover_r2 l μ h4 hl hμ hlo hhi with
    ⟨q, h, rfl, rfl, h1, h2⟩ | ⟨k, h, rfl, rfl, h1, h2, h3⟩ | ⟨k, h, rfl, rfl, h1, h2⟩ | ⟨k, rfl, rfl, h1⟩
  · exact band_of (famFA_sp q h h1 h2) (by omega)
  · exact band_of (famFB2_sp k h h1 h2 h3) (by omega)
  · exact band_of (famFB6_sp k h h1 h2) (by omega)
  · exact band_of (famF4_sp k h1) (by omega)

/-- The band for `l ≡ 3 (mod 4)`: the families `R3T1`, `R3O`, `R3E`, `R3Q`, and `τ_l` at `μ = l`. -/
theorem band_r3 (l μ : ℤ) (h4 : l % 4 = 3) (hl : 7 ≤ l) (hμ : μ % 2 = 1) (hlo : l < 2 * μ)
    (hhi : μ ≤ l) : ∃ G, SP l ((μ + 1) / 2) G := by
  rcases cover_r3 l μ h4 hl hμ hlo hhi with
    ⟨q, rfl, rfl, h1⟩ | ⟨q, u, rfl, rfl, h1, h2⟩ | ⟨q, u, rfl, rfl, h1, h2⟩ | ⟨q, u, rfl, rfl, h1, h2⟩ | rfl
  · exact band_of (famR3T1_sp q h1) (by omega)
  · exact band_of (famR3O_sp q u h1 h2) (by omega)
  · exact band_of (famR3E_sp q u h1 h2) (by omega)
  · exact band_of (famR3Q_sp q u h1 h2) (by omega)
  · exact ⟨_, SP.tau _ (by omega) hμ⟩

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
