import L2.Band

/-!
# The signed-permutation problem on the whole cone

`SP(l, δ)` has a solution for every `l ≥ 5` and every `δ` with `1 − l ≤ 2δ − 1 ≤ l`. Inversion
reduces to `δ ≥ 1`. Writing `μ = 2δ − 1`: `μ = 1` is the reversal, `μ = l` the two-block reversal,
`l < 2μ` the band; otherwise the step from order `l − μ` to order `l` at the same `μ` reduces the
order, down to a base in the band, to `τ_μ`, or to the explicit solution of `SP(7, 2)`.
-/

namespace L2

/-- The cone for `δ ≥ 1`, by induction on a bound `n` for the order. -/
theorem cone_sp_pos (n : ℕ) : ∀ l δ : ℤ, l ≤ n → 5 ≤ l → 1 ≤ δ → 2 * δ - 1 ≤ l →
    ∃ G, SP l δ G := by
  sorry

/-- `SP(l, δ)` on the whole cone `1 − l ≤ 2δ − 1 ≤ l`, `l ≥ 5`. -/
theorem cone_sp (l δ : ℤ) (hl : 5 ≤ l) (hlo : 1 - l ≤ 2 * δ - 1) (hhi : 2 * δ - 1 ≤ l) :
    ∃ G, SP l δ G := by
  by_cases hδ : 1 ≤ δ
  · exact cone_sp_pos l.toNat l δ (by omega) hl hδ hhi
  · obtain ⟨G, hG⟩ := cone_sp_pos l.toNat l (1 - δ) (by omega) hl (by omega) (by omega)
    have h' := hG.inv
    rw [sub_sub_cancel] at h'
    exact ⟨_, h'⟩

end L2
