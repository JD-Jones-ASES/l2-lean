import L2.Band

/-!
# The signed-permutation problem on the whole cone

`SP(l, δ)` has a solution for every `l ≥ 5` and every `δ` with `−l ≤ 2δ − 1 ≤ l`. Inversion
reduces to `δ ≥ 1`. Writing `μ = 2δ − 1`: `μ = 1` is the reversal, `μ = l` the two-block reversal,
`l < 2μ` the band; otherwise the step from order `l − μ` to order `l` at the same `μ` reduces the
order, down to a base in the band, to `τ_μ`, or to the explicit solution of `SP(7, 2)`.
-/

namespace L2

/-- The cone for `δ ≥ 1`, by induction on a bound `n` for the order. With `μ = 2δ − 1`, the cells
`μ = 1` (the reversal), `μ = l` (`τ_l`) and `l < 2μ` (the band) are direct; every other cell is the
step at fixed `μ` from order `l − μ ≥ μ`, where the smaller cell is `τ_μ`, a band cell, a smaller
cell of the cone, or (when `μ = 3` and `l = 7`) replaced by the explicit solution of `SP(7, 2)`. -/
theorem cone_sp_pos (n : ℕ) : ∀ l δ : ℤ, l ≤ n → 5 ≤ l → 1 ≤ δ → 2 * δ - 1 ≤ l →
    ∃ G, SP l δ G := by
  induction n with
  | zero => intro l δ hn hl; omega
  | succ n ih =>
    intro l δ hn hl hδ hμ
    push_cast at hn
    have e : (2 * δ - 1 + 1) / 2 = δ := by omega
    have hodd : (2 * δ - 1) % 2 = 1 := by omega
    by_cases h1 : δ = 1
    · subst h1
      exact ⟨_, SP.reversal l (by omega)⟩
    by_cases h2 : 2 * δ - 1 = l
    · have t := SP.tau l (by omega) (by omega)
      have e' : (l + 1) / 2 = δ := by omega
      rw [e'] at t
      exact ⟨_, t⟩
    by_cases h3 : l < 2 * (2 * δ - 1)
    · obtain ⟨G, hG⟩ := band_sp l (2 * δ - 1) hl hodd h3 hμ
      rw [e] at hG
      exact ⟨_, hG⟩
    -- `2μ ≤ l`: the cell is the step from order `l' = l − μ ≥ μ`
    have hsum : l - (2 * δ - 1) + (2 * δ - 1) = l := by omega
    by_cases h4 : l - (2 * δ - 1) = 2 * δ - 1
    · have t := SP.tau (2 * δ - 1) (by omega) hodd
      rw [e] at t
      have c := t.cinv hδ
      have e' : 2 * δ - 1 + (2 * δ - 1) = l := by omega
      rw [e'] at c
      exact ⟨_, c⟩
    by_cases h5 : l - (2 * δ - 1) < 2 * (2 * δ - 1)
    · by_cases h6 : 5 ≤ l - (2 * δ - 1)
      · obtain ⟨G, hG⟩ := band_sp (l - (2 * δ - 1)) (2 * δ - 1) h6 hodd h5 (by omega)
        rw [e] at hG
        have c := hG.cinv hδ
        rw [hsum] at c
        exact ⟨_, c⟩
      · -- `μ < l' ≤ 4` forces `μ = 3` and `l' = 4`: the cell `SP(7, 2)`
        have hδ2 : δ = 2 := by omega
        have hl7 : l = 7 := by omega
        subst hδ2 hl7
        exact ⟨_, sp_7_3⟩
    · obtain ⟨G, hG⟩ := ih (l - (2 * δ - 1)) δ (by omega) (by omega) hδ (by omega)
      have c := hG.cinv hδ
      rw [hsum] at c
      exact ⟨_, c⟩

/-- `SP(l, δ)` on the whole cone `−l ≤ 2δ − 1 ≤ l`, `l ≥ 5`; the cell `μ = −l` is the inverse of `τ_l`. -/
theorem cone_sp (l δ : ℤ) (hl : 5 ≤ l) (hlo : -l ≤ 2 * δ - 1) (hhi : 2 * δ - 1 ≤ l) :
    ∃ G, SP l δ G := by
  by_cases hδ : 1 ≤ δ
  · exact cone_sp_pos l.toNat l δ (by omega) hl hδ hhi
  · obtain ⟨G, hG⟩ := cone_sp_pos l.toNat l (1 - δ) (by omega) hl (by omega) (by omega)
    have h' := hG.inv
    rw [sub_sub_cancel] at h'
    exact ⟨_, h'⟩

end L2
