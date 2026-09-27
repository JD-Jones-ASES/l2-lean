import L2.Rows

/-!
# The signed-permutation problem

`SP(l, δ)` asks for a permutation `σ` of `[1, l]` whose values `σ(w) − w + δ`, together with their
mirrors `1 − (σ(w) − w + δ)`, are exactly `[1 − l, l]`. It is stated here in graph form. Inversion
exchanges `δ` and `1 − δ`; the reversal solves `δ = 1`; the two-block reversal `τ_l` solves
`δ = (l + 1)/2` for odd `l`; and appending `τ_μ` to a solution and inverting (with `μ = 2δ − 1`)
steps from order `n` to order `n + μ` at the same `δ`, which gives the descent along each line of
fixed `μ`.
-/

namespace L2
noncomputable section

/-- A solution of `SP(l, δ)`: `G` is the graph of a permutation of `[1, l]` (sources and targets
`[1, l]`, at most `l` arrows) whose values `t − w + δ` and mirrors `w − t + 1 − δ` together tile
`[1 − l, l]`. -/
structure SP (l δ : ℤ) (G : Finset (ℤ × ℤ)) : Prop where
  order_pos : 1 ≤ l
  sources : G.image Prod.fst = Finset.Icc 1 l
  targets : G.image Prod.snd = Finset.Icc 1 l
  values : G.image (val δ) ∪ G.image (mir δ) = Finset.Icc (1 - l) l
  card_le : G.card ≤ l.toNat

/-- Inversion: the inverse permutation solves `SP(l, 1 − δ)`. -/
theorem SP.inv {l δ : ℤ} {G : Finset (ℤ × ℤ)} (h : SP l δ G) :
    SP l (1 - δ) (G.image Prod.swap) where
  order_pos := h.order_pos
  sources := by
    rw [Finset.image_image]
    simpa [Function.comp_def] using h.targets
  targets := by
    rw [Finset.image_image]
    simpa [Function.comp_def] using h.sources
  values := by
    ext x
    rw [Finset.mem_union, mem_image_val_swap, mem_image_mir_swap, sub_sub_cancel, or_comm,
      ← Finset.mem_union, h.values]
  card_le := Finset.card_image_le.trans h.card_le

/-- The reversal `w ↦ l + 1 − w` solves `SP(l, 1)` (`μ = 1`). -/
theorem SP.reversal (l : ℤ) (hl : 1 ≤ l) : SP l 1 (row 0 0 l) := by
  refine ⟨hl, ?_, ?_, ?_, card_row_le _ _ _⟩
  · ext x
    simp only [mem_image_fst_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [mem_image_snd_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [Finset.mem_union, mem_image_val_row, mem_image_mir_row, Finset.mem_Icc]
    omega

/-- `τ_l` for odd `l`: reverse `[1, (l+1)/2]` and `[(l+3)/2, l]`. -/
def tauGraph (l : ℤ) : Finset (ℤ × ℤ) :=
  row 0 0 ((l + 1) / 2) ∪ row ((l + 1) / 2) ((l + 1) / 2) ((l - 1) / 2)

/-- `τ_l` solves `SP(l, (l+1)/2)` for odd `l` (`μ = l`). -/
theorem SP.tau (l : ℤ) (hl : 1 ≤ l) (hodd : l % 2 = 1) : SP l ((l + 1) / 2) (tauGraph l) := by
  obtain ⟨h, rfl⟩ : ∃ h, l = 2 * h - 1 := ⟨(l + 1) / 2, by omega⟩
  have e1 : (2 * h - 1 + 1) / 2 = h := by omega
  have e2 : (2 * h - 1 - 1) / 2 = h - 1 := by omega
  unfold tauGraph
  rw [e1, e2]
  refine ⟨hl, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [image_union_fst, Finset.mem_union, mem_image_fst_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [image_union_snd, Finset.mem_union, mem_image_snd_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc]
    omega
  · exact (card_union_le_of_le (card_row_le _ _ _) (card_row_le _ _ _)).trans (by omega)

/-- The composite of the step to order `n + μ` with inversion, `μ = 2δ − 1`: shift the targets of a
solution of `SP(n, δ)` by `μ`, place `τ_μ` on the new sources `[n + 1, n + μ]` with targets
`[1, μ]`, and invert. -/
def cinvGraph (n δ : ℤ) (G : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  (G.image (fun q => (q.1, q.2 + (2 * δ - 1))) ∪
    (tauGraph (2 * δ - 1)).image (fun q => (q.1 + n, q.2))).image Prod.swap

/-- The step: from `SP(n, δ)` with `δ ≥ 1`, shifting the targets by `μ = 2δ − 1` and appending
`τ_μ` on the new sources solves `SP(n + μ, 1 − δ)`. -/
theorem SP.cinv_aux {n δ : ℤ} {G : Finset (ℤ × ℤ)} (h : SP n δ G) (hδ : 1 ≤ δ) :
    SP (n + (2 * δ - 1)) (1 - δ)
      (G.image (fun q => (q.1, q.2 + (2 * δ - 1))) ∪
        (tauGraph (2 * δ - 1)).image (fun q => (q.1 + n, q.2))) := by
  sorry

/-- The step followed by inversion: from `SP(n, δ)` with `δ ≥ 1`, a solution of `SP(n + μ, δ)`,
`μ = 2δ − 1`. -/
theorem SP.cinv {n δ : ℤ} {G : Finset (ℤ × ℤ)} (h : SP n δ G) (hδ : 1 ≤ δ) :
    SP (n + (2 * δ - 1)) δ (cinvGraph n δ G) := by
  have h' := (h.cinv_aux hδ).inv
  rw [sub_sub_cancel] at h'
  exact h'

/-- The descent along the line of fixed `μ = 2δ − 1`: `k` steps. -/
theorem SP.descend {n δ : ℤ} {G : Finset (ℤ × ℤ)} (h : SP n δ G) (hδ : 1 ≤ δ) (k : ℕ) :
    ∃ G', SP (n + k * (2 * δ - 1)) δ G' := by
  induction k with
  | zero => exact ⟨G, by simpa using h⟩
  | succ k ih =>
    obtain ⟨G', hG'⟩ := ih
    have h' := hG'.cinv hδ
    refine ⟨cinvGraph (n + k * (2 * δ - 1)) δ G', ?_⟩
    convert h' using 1
    push_cast
    ring

end
end L2
