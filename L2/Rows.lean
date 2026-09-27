import L2.Pairs

/-!
# Block-reversal rows

A permutation of `[1, l]` is given by its graph, a finite set of arrows `(w, t)` with `t` the
image of `w`. The families of this development are unions of *rows*: a row reverses a block of
consecutive sources onto a block of consecutive targets. For an arrow `(w, t)` and a shift `δ`, the
value is `t − w + δ` and the mirror value is `1 − (t − w + δ)`. Along a row both run through an
arithmetic progression of step two, which the four membership lemmas below make explicit.
-/

namespace L2
noncomputable section

/-- The row of `n` arrows `a + r ↦ c + n + 1 − r`, `1 ≤ r ≤ n`: sources `[a+1, a+n]`, targets
`[c+1, c+n]` reversed. -/
def row (a c n : ℤ) : Finset (ℤ × ℤ) := (Finset.Icc 1 n).image fun r => (a + r, c + n + 1 - r)

/-- The value of an arrow `(w, t)` at shift `δ`. -/
def val (δ : ℤ) (q : ℤ × ℤ) : ℤ := q.2 - q.1 + δ

/-- The mirror value of an arrow `(w, t)` at shift `δ`, namely `1 − val δ (w, t)`. -/
def mir (δ : ℤ) (q : ℤ × ℤ) : ℤ := q.1 - q.2 + 1 - δ

/-- The sources of a row are `[a + 1, a + n]`. -/
theorem mem_image_fst_row (a c n x : ℤ) :
    x ∈ (row a c n).image Prod.fst ↔ a + 1 ≤ x ∧ x ≤ a + n := by
  simp only [row, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    dsimp only
    omega
  · intro hx
    refine ⟨(a + (x - a), c + n + 1 - (x - a)), ⟨x - a, ?_, rfl⟩, ?_⟩ <;> (try dsimp only) <;> omega

/-- The targets of a row are `[c + 1, c + n]`. -/
theorem mem_image_snd_row (a c n x : ℤ) :
    x ∈ (row a c n).image Prod.snd ↔ c + 1 ≤ x ∧ x ≤ c + n := by
  simp only [row, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    dsimp only
    omega
  · intro hx
    refine ⟨(a + (c + n + 1 - x), c + n + 1 - (c + n + 1 - x)), ⟨c + n + 1 - x, ?_, rfl⟩, ?_⟩ <;>
      (try dsimp only) <;> omega

/-- `val δ (a+r, c+n+1−r) = c − a + n + 1 + δ − 2r`: along a row the values are the step-two run
from `c − a + 1 − n + δ` up to `c − a + n − 1 + δ`. -/
theorem mem_image_val_row (δ a c n x : ℤ) :
    x ∈ (row a c n).image (val δ) ↔
      c - a + 1 - n + δ ≤ x ∧ x ≤ c - a + n - 1 + δ ∧ (x - (c - a + n - 1 + δ)) % 2 = 0 := by
  simp only [row, val, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    dsimp only
    omega
  · intro hx
    refine ⟨(a + (c - a + n + 1 + δ - x) / 2, c + n + 1 - (c - a + n + 1 + δ - x) / 2),
      ⟨(c - a + n + 1 + δ - x) / 2, ?_, rfl⟩, ?_⟩ <;> (try dsimp only) <;> omega

/-- `mir δ (a+r, c+n+1−r) = a − c − n − δ + 2r`: along a row the mirror values are the step-two
run from `a − c + 2 − n − δ` up to `a − c + n − δ`. -/
theorem mem_image_mir_row (δ a c n x : ℤ) :
    x ∈ (row a c n).image (mir δ) ↔
      a - c + 2 - n - δ ≤ x ∧ x ≤ a - c + n - δ ∧ (x - (a - c + n - δ)) % 2 = 0 := by
  simp only [row, mir, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    dsimp only
    omega
  · intro hx
    refine ⟨(a + (x - (a - c - n - δ)) / 2, c + n + 1 - (x - (a - c - n - δ)) / 2),
      ⟨(x - (a - c - n - δ)) / 2, ?_, rfl⟩, ?_⟩ <;> (try dsimp only) <;> omega

/-- A row of length `n` has at most `n` arrows. -/
theorem card_row_le (a c n : ℤ) : (row a c n).card ≤ n.toNat := by
  unfold row
  exact Finset.card_image_le.trans_eq (by simp)

/-- Sources of a union. -/
@[simp] theorem image_union_fst (G H : Finset (ℤ × ℤ)) :
    (G ∪ H).image Prod.fst = G.image Prod.fst ∪ H.image Prod.fst :=
  Finset.image_union _ _

/-- Targets of a union. -/
@[simp] theorem image_union_snd (G H : Finset (ℤ × ℤ)) :
    (G ∪ H).image Prod.snd = G.image Prod.snd ∪ H.image Prod.snd :=
  Finset.image_union _ _

/-- Values of a union. -/
@[simp] theorem image_union_val (δ : ℤ) (G H : Finset (ℤ × ℤ)) :
    (G ∪ H).image (val δ) = G.image (val δ) ∪ H.image (val δ) :=
  Finset.image_union _ _

/-- Mirror values of a union. -/
@[simp] theorem image_union_mir (δ : ℤ) (G H : Finset (ℤ × ℤ)) :
    (G ∪ H).image (mir δ) = G.image (mir δ) ∪ H.image (mir δ) :=
  Finset.image_union _ _

/-- Inverting the permutation turns values at `δ` into mirror values at `1 − δ`. -/
theorem mem_image_val_swap (δ : ℤ) (G : Finset (ℤ × ℤ)) (x : ℤ) :
    x ∈ (G.image Prod.swap).image (val δ) ↔ x ∈ G.image (mir (1 - δ)) := by
  have h : val δ ∘ Prod.swap = mir (1 - δ) := by
    funext q
    simp only [Function.comp_apply, val, mir, Prod.fst_swap, Prod.snd_swap]
    ring
  rw [Finset.image_image, h]

/-- Inverting the permutation turns mirror values at `δ` into values at `1 − δ`. -/
theorem mem_image_mir_swap (δ : ℤ) (G : Finset (ℤ × ℤ)) (x : ℤ) :
    x ∈ (G.image Prod.swap).image (mir δ) ↔ x ∈ G.image (val (1 - δ)) := by
  have h : mir δ ∘ Prod.swap = val (1 - δ) := by
    funext q
    simp only [Function.comp_apply, val, mir, Prod.fst_swap, Prod.snd_swap]
    ring
  rw [Finset.image_image, h]

end
end L2
