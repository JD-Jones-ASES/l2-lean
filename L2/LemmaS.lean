import L2.SP
import L2.Multi

/-!
# From the signed-permutation problem to a two-fold sequence

A solution `σ` of `SP(l, δ)` gives a mirror-symmetric two-fold Langford sequence of order `l` and
defect `l + δ` on `[1, 4l]`. With `y = σ(w) − w + δ`, the first colour has the outer pairs
`(l + 1 − w, 2l + y)` and the second the inner pairs `(2l + 1 − y, 3l + w)`; both colours have the
differences `l + σ(w) + δ − 1`, which run over `[l + δ, 2l + δ − 1]`, and the middle ends `2l + y`
and `2l + 1 − y` fill `[l + 1, 3l]` exactly because the values and their mirrors tile `[1 − l, l]`.
-/

namespace L2
noncomputable section

/-- The outer pairs `(l + 1 − w, 2l + y)`, `y = t − w + δ`, for the arrows `(w, t)` of `G`. -/
def colourA (δ l : ℤ) (G : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  G.image fun q => (l + 1 - q.1, 2 * l + q.2 - q.1 + δ)

/-- The inner pairs `(2l + 1 − y, 3l + w)`, `y = t − w + δ`, for the arrows `(w, t)` of `G`. -/
def colourB (δ l : ℤ) (G : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  G.image fun q => (2 * l + q.1 - q.2 + 1 - δ, 3 * l + q.1)

/-- The endpoints of the outer pairs: `l + 1 − w` for a source `w`, and `2l + y` for a value `y`. -/
theorem mem_pairEndpoints_colourA (δ l : ℤ) (G : Finset (ℤ × ℤ)) (x : ℤ) :
    x ∈ pairEndpoints (colourA δ l G) ↔
      l + 1 - x ∈ G.image Prod.fst ∨ x - 2 * l ∈ G.image (val δ) := by
  simp only [pairEndpoints, colourA, val, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨q, hq, by omega⟩
    · exact Or.inr ⟨q, hq, by omega⟩
  · rintro (⟨q, hq, hx⟩ | ⟨q, hq, hx⟩)
    · exact ⟨_, ⟨q, hq, rfl⟩, Or.inl (show x = l + 1 - q.1 by omega)⟩
    · exact ⟨_, ⟨q, hq, rfl⟩, Or.inr (show x = 2 * l + q.2 - q.1 + δ by omega)⟩

/-- The endpoints of the inner pairs: `2l + y'` for a mirror value `y'`, and `3l + w` for a source
`w`. -/
theorem mem_pairEndpoints_colourB (δ l : ℤ) (G : Finset (ℤ × ℤ)) (x : ℤ) :
    x ∈ pairEndpoints (colourB δ l G) ↔
      x - 2 * l ∈ G.image (mir δ) ∨ x - 3 * l ∈ G.image Prod.fst := by
  simp only [pairEndpoints, colourB, mir, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨q, hq, by omega⟩
    · exact Or.inr ⟨q, hq, by omega⟩
  · rintro (⟨q, hq, hx⟩ | ⟨q, hq, hx⟩)
    · exact ⟨_, ⟨q, hq, rfl⟩, Or.inl (show x = 2 * l + q.1 - q.2 + 1 - δ by omega)⟩
    · exact ⟨_, ⟨q, hq, rfl⟩, Or.inr (show x = 3 * l + q.1 by omega)⟩

/-- Both colours have the difference `l + t + δ − 1` on the arrow `(w, t)`, so the differences of a
colour built from a permutation graph with targets `[1, l]` are `[l + δ, 2l + δ − 1]`. -/
theorem pairDifferences_image_of_targets {l δ : ℤ} {G : Finset (ℤ × ℤ)}
    (ht : G.image Prod.snd = Finset.Icc 1 l) (f : ℤ × ℤ → ℤ × ℤ)
    (hf : ∀ q, (f q).2 - (f q).1 = l + q.2 + δ - 1) :
    pairDifferences (G.image f) = Finset.Icc (l + δ) (l + δ + l - 1) := by
  ext x
  have hmem (t : ℤ) : (∃ q ∈ G, q.2 = t) ↔ 1 ≤ t ∧ t ≤ l := by
    rw [← Finset.mem_Icc, ← ht, Finset.mem_image]
  simp only [pairDifferences, Finset.image_image, Finset.mem_image, Function.comp_apply, hf,
    Finset.mem_Icc]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have := (hmem q.2).mp ⟨q, hq, rfl⟩
    omega
  · intro hx
    obtain ⟨q, hq, hq2⟩ := (hmem (x - l - δ + 1)).mpr (by omega)
    exact ⟨q, hq, by omega⟩

/-- A solution of `SP(l, δ)` gives a two-fold Langford sequence of order `l` and defect `l + δ`. -/
theorem SP.toTwoFold {l δ : ℤ} {G : Finset (ℤ × ℤ)} (h : SP l δ G) (hd : 1 ≤ l + δ) :
    TwoFold (l + δ) l (colourA δ l G) (colourB δ l G) := by
  refine ⟨hd, h.order_pos, ?_, ?_, ?_, Finset.card_image_le.trans h.card_le,
    Finset.card_image_le.trans h.card_le⟩
  · exact pairDifferences_image_of_targets h.targets _ fun q => by ring
  · exact pairDifferences_image_of_targets h.targets _ fun q => by ring
  · ext x
    have hv : x - 2 * l ∈ G.image (val δ) ∨ x - 2 * l ∈ G.image (mir δ) ↔
        1 - l ≤ x - 2 * l ∧ x - 2 * l ≤ l := by
      rw [← Finset.mem_union, h.values, Finset.mem_Icc]
    rw [pairEndpoints_union, Finset.mem_union, mem_pairEndpoints_colourA,
      mem_pairEndpoints_colourB, h.sources]
    simp only [Finset.mem_Icc]
    constructor
    · rintro ((hx | hx) | (hx | hx))
      · omega
      · have := hv.mp (Or.inl hx); omega
      · have := hv.mp (Or.inr hx); omega
      · omega
    · intro hx
      by_cases h1 : x ≤ l
      · exact Or.inl (Or.inl (by omega))
      · by_cases h3 : 3 * l < x
        · exact Or.inr (Or.inr (by omega))
        · rcases hv.mpr (by omega) with hx' | hx'
          · exact Or.inl (Or.inr hx')
          · exact Or.inr (Or.inl hx')

end
end L2
