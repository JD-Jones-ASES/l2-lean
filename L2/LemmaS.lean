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
  sorry

/-- The endpoints of the inner pairs: `2l + y'` for a mirror value `y'`, and `3l + w` for a source
`w`. -/
theorem mem_pairEndpoints_colourB (δ l : ℤ) (G : Finset (ℤ × ℤ)) (x : ℤ) :
    x ∈ pairEndpoints (colourB δ l G) ↔
      x - 2 * l ∈ G.image (mir δ) ∨ x - 3 * l ∈ G.image Prod.fst := by
  sorry

/-- A solution of `SP(l, δ)` gives a two-fold Langford sequence of order `l` and defect `l + δ`. -/
theorem SP.toTwoFold {l δ : ℤ} {G : Finset (ℤ × ℤ)} (h : SP l δ G) (hd : 1 ≤ l + δ) :
    TwoFold (l + δ) l (colourA δ l G) (colourB δ l G) := by
  sorry

end
end L2
