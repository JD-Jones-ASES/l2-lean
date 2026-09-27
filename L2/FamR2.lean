import L2.SP

/-!
# Block-reversal families for `l ≡ 2 (mod 4)`

The families `FA`, `FB2`, `FB6`, `F4`. Each is a union of rows (block reversals) whose sizes
are affine in the parameters, and each solves `SP(l, δ)` on its whole domain: the value runs
and mirror runs of its rows tile `[1 − l, l]`.

Each proof is the family's class table, mechanised. The sources and the targets of the blocks
tile `[1, l]`. Every value run and every mirror run lies inside `[1 − l, l]`. Conversely, an `x`
in `[1 − l, l]` is placed by its sign and its parity: in each of the four cases the class table
(kept as a comment under each theorem) names a chain of runs, abutting with step two, that covers
that class, and splitting `x` at the chain's boundaries leaves one run per piece.
-/

namespace L2

/-- The block-reversal family `FA` (l = 4q + 2, μ = 2h - 1, 5 blocks, target order `23041`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famFA (q h : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (4 * q + 3 - 2 * h) (h - 1) ∪
    row (h - 1) (3 * q + 1) (q + 1) ∪
    row (q + h) 0 (3 * q + 3 - 2 * h) ∪
    row (4 * q + 3 - h) (3 * q + 3 - 2 * h) q ∪
    row (5 * q + 3 - h) (4 * q + 2 - h) (h - q - 1)

/-- The family `FA` solves `SP(l, δ)` with `l = 4 * q + 2`, `δ = h` (`μ = 2 * h - 1`) on its whole domain. -/
theorem famFA_sp (q h : ℤ)
    (h1 : q + 2 ≤ h) (h2 : 2 * h ≤ 3 * q + 2) :
    SP (4 * q + 2) (h) (famFA q h) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [famFA, image_union_fst, Finset.mem_union, mem_image_fst_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famFA, image_union_snd, Finset.mem_union, mem_image_snd_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famFA, image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc]
    constructor
    · intro hx
      omega
    · intro hx
      simp only [or_assoc]
      rcases le_or_gt 1 x with hs | hs <;> rcases Int.emod_two_eq x with hp | hp
      · rcases le_or_gt x (2 * q) with c1 | c1 <;>
          repeat (first | (left; omega) | right | omega)
      · rcases le_or_gt x (2 * h - 2 * q - 3) with c1 | c1 <;>
          rcases le_or_gt x (4 * q + 3 - 2 * h) with c2 | c2 <;>
          repeat (first | (left; omega) | right | omega)
      · rcases le_or_gt x (2 * h - 4 * q - 4) with c1 | c1 <;>
          rcases le_or_gt x (2 * q + 2 - 2 * h) with c2 | c2 <;>
          repeat (first | (left; omega) | right | omega)
      · rcases le_or_gt x (-2 * q - 1) with c1 | c1 <;>
          repeat (first | (left; omega) | right | omega)
  · unfold famFA
    exact (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le
      (card_union_le_of_le (card_row_le _ _ _) (card_row_le _ _ _)) (card_row_le _ _ _))
      (card_row_le _ _ _)) (card_row_le _ _ _)).trans (by omega)
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 4 * q + 3 - 2 * h, n = h - 1; value [4 * q + 5 - 2 * h, 4 * q + 1]; mirror [-4 * q, 2 * h - 4 * q - 4]; P
--   b1: a = h - 1, c = 3 * q + 1, n = q + 1; value [2 * q + 2, 4 * q + 2]; mirror [-4 * q - 1, -2 * q - 1]; P
--   b2: a = q + h, c = 0, n = 3 * q + 3 - 2 * h; value [2 * h - 4 * q - 2, 2 * q + 2 - 2 * h]; mirror [2 * h - 2 * q - 1, 4 * q + 3 - 2 * h]; N
--   b3: a = 4 * q + 3 - h, c = 3 * q + 3 - 2 * h, n = q; value [1 - 2 * q, -1]; mirror [2, 2 * q]; N
--   b4: a = 5 * q + 3 - h, c = 4 * q + 2 - h, n = h - q - 1; value [1, 2 * h - 2 * q - 3]; mirror [2 * q + 4 - 2 * h, 0]; P
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b4.value [1, 2 * h - 2 * q - 3] | b2.mirror [2 * h - 2 * q - 1, 4 * q + 3 - 2 * h] | b0.value [4 * q + 5 - 2 * h, 4 * q + 1]
--   x ≥ 1, x even: b3.mirror [2, 2 * q] | b1.value [2 * q + 2, 4 * q + 2]
--   x ≤ 0, x odd: b1.mirror [-4 * q - 1, -2 * q - 1] | b3.value [1 - 2 * q, -1]
--   x ≤ 0, x even: b0.mirror [-4 * q, 2 * h - 4 * q - 4] | b2.value [2 * h - 4 * q - 2, 2 * q + 2 - 2 * h] | b4.mirror [2 * q + 4 - 2 * h, 0]

/-- The block-reversal family `FB2` (l = 8k + 2, μ = 2h - 1, 5 blocks, target order `13042`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famFB2 (k h : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (9 * k + 3 - 2 * h) (h - k - 1) ∪
    row (h - k - 1) 0 k ∪
    row (h - 1) (5 * k + 1) (3 * k + 1) ∪
    row (3 * k + h) k (8 * k + 3 - 2 * h) ∪
    row (11 * k + 3 - h) (8 * k + 2 - h) (h - 3 * k - 1)

/-- The family `FB2` solves `SP(l, δ)` with `l = 8 * k + 2`, `δ = h` (`μ = 2 * h - 1`) on its whole domain. -/
theorem famFB2_sp (k h : ℤ)
    (h1 : 1 ≤ k) (h2 : 3 * k + 2 ≤ h) (h3 : h ≤ 4 * k + 1) :
    SP (8 * k + 2) (h) (famFB2 k h) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [famFB2, image_union_fst, Finset.mem_union, mem_image_fst_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famFB2, image_union_snd, Finset.mem_union, mem_image_snd_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famFB2, image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc]
    constructor
    · intro hx
      omega
    · intro hx
      simp only [or_assoc]
      rcases le_or_gt 1 x with hs | hs <;> rcases Int.emod_two_eq x with hp | hp
      · rcases le_or_gt x (2 * k) with c1 | c1 <;>
          repeat (first | (left; omega) | right | omega)
      · rcases le_or_gt x (2 * h - 6 * k - 3) with c1 | c1 <;>
          rcases le_or_gt x (10 * k + 3 - 2 * h) with c2 | c2 <;>
          repeat (first | (left; omega) | right | omega)
      · rcases le_or_gt x (2 * h - 10 * k - 4) with c1 | c1 <;>
          rcases le_or_gt x (6 * k + 2 - 2 * h) with c2 | c2 <;>
          repeat (first | (left; omega) | right | omega)
      · rcases le_or_gt x (-2 * k - 1) with c1 | c1 <;>
          repeat (first | (left; omega) | right | omega)
  · unfold famFB2
    exact (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le
      (card_union_le_of_le (card_row_le _ _ _) (card_row_le _ _ _)) (card_row_le _ _ _))
      (card_row_le _ _ _)) (card_row_le _ _ _)).trans (by omega)
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 9 * k + 3 - 2 * h, n = h - k - 1; value [10 * k + 5 - 2 * h, 8 * k + 1]; mirror [-8 * k, 2 * h - 10 * k - 4]; P
--   b1: a = h - k - 1, c = 0, n = k; value [2, 2 * k]; mirror [1 - 2 * k, -1]; P
--   b2: a = h - 1, c = 5 * k + 1, n = 3 * k + 1; value [2 * k + 2, 8 * k + 2]; mirror [-8 * k - 1, -2 * k - 1]; P
--   b3: a = 3 * k + h, c = k, n = 8 * k + 3 - 2 * h; value [2 * h - 10 * k - 2, 6 * k + 2 - 2 * h]; mirror [2 * h - 6 * k - 1, 10 * k + 3 - 2 * h]; N
--   b4: a = 11 * k + 3 - h, c = 8 * k + 2 - h, n = h - 3 * k - 1; value [1, 2 * h - 6 * k - 3]; mirror [6 * k + 4 - 2 * h, 0]; P
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b4.value [1, 2 * h - 6 * k - 3] | b3.mirror [2 * h - 6 * k - 1, 10 * k + 3 - 2 * h] | b0.value [10 * k + 5 - 2 * h, 8 * k + 1]
--   x ≥ 1, x even: b1.value [2, 2 * k] | b2.value [2 * k + 2, 8 * k + 2]
--   x ≤ 0, x odd: b2.mirror [-8 * k - 1, -2 * k - 1] | b1.mirror [1 - 2 * k, -1]
--   x ≤ 0, x even: b0.mirror [-8 * k, 2 * h - 10 * k - 4] | b3.value [2 * h - 10 * k - 2, 6 * k + 2 - 2 * h] | b4.mirror [6 * k + 4 - 2 * h, 0]

/-- The block-reversal family `FB6` (l = 8k + 6, μ = 2h - 1, 5 blocks, target order `13042`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famFB6 (k h : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (9 * k + 8 - 2 * h) (h - k - 1) ∪
    row (h - k - 1) 0 (k + 1) ∪
    row h (5 * k + 4) (3 * k + 2) ∪
    row (3 * k + h + 2) (k + 1) (8 * k + 7 - 2 * h) ∪
    row (11 * k + 9 - h) (8 * k + 7 - h) (h - 3 * k - 3)

/-- The family `FB6` solves `SP(l, δ)` with `l = 8 * k + 6`, `δ = h` (`μ = 2 * h - 1`) on its whole domain. -/
theorem famFB6_sp (k h : ℤ)
    (h1 : 3 * k + 4 ≤ h) (h2 : h ≤ 4 * k + 3) :
    SP (8 * k + 6) (h) (famFB6 k h) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [famFB6, image_union_fst, Finset.mem_union, mem_image_fst_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famFB6, image_union_snd, Finset.mem_union, mem_image_snd_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famFB6, image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc]
    constructor
    · intro hx
      omega
    · intro hx
      simp only [or_assoc]
      rcases le_or_gt 1 x with hs | hs <;> rcases Int.emod_two_eq x with hp | hp
      · rcases le_or_gt x (2 * h - 6 * k - 6) with c1 | c1 <;>
          rcases le_or_gt x (10 * k + 8 - 2 * h) with c2 | c2 <;>
          repeat (first | (left; omega) | right | omega)
      · rcases le_or_gt x (2 * k + 1) with c1 | c1 <;>
          repeat (first | (left; omega) | right | omega)
      · rcases le_or_gt x (-2 * k - 2) with c1 | c1 <;>
          repeat (first | (left; omega) | right | omega)
      · rcases le_or_gt x (2 * h - 10 * k - 9) with c1 | c1 <;>
          rcases le_or_gt x (6 * k + 5 - 2 * h) with c2 | c2 <;>
          repeat (first | (left; omega) | right | omega)
  · unfold famFB6
    exact (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le
      (card_union_le_of_le (card_row_le _ _ _) (card_row_le _ _ _)) (card_row_le _ _ _))
      (card_row_le _ _ _)) (card_row_le _ _ _)).trans (by omega)
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 9 * k + 8 - 2 * h, n = h - k - 1; value [10 * k + 10 - 2 * h, 8 * k + 6]; mirror [-8 * k - 5, 2 * h - 10 * k - 9]; P
--   b1: a = h - k - 1, c = 0, n = k + 1; value [1, 2 * k + 1]; mirror [-2 * k, 0]; P
--   b2: a = h, c = 5 * k + 4, n = 3 * k + 2; value [2 * k + 3, 8 * k + 5]; mirror [-8 * k - 4, -2 * k - 2]; P
--   b3: a = 3 * k + h + 2, c = k + 1, n = 8 * k + 7 - 2 * h; value [2 * h - 10 * k - 7, 6 * k + 5 - 2 * h]; mirror [2 * h - 6 * k - 4, 10 * k + 8 - 2 * h]; N
--   b4: a = 11 * k + 9 - h, c = 8 * k + 7 - h, n = h - 3 * k - 3; value [2, 2 * h - 6 * k - 6]; mirror [6 * k + 7 - 2 * h, -1]; P
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b1.value [1, 2 * k + 1] | b2.value [2 * k + 3, 8 * k + 5]
--   x ≥ 1, x even: b4.value [2, 2 * h - 6 * k - 6] | b3.mirror [2 * h - 6 * k - 4, 10 * k + 8 - 2 * h] | b0.value [10 * k + 10 - 2 * h, 8 * k + 6]
--   x ≤ 0, x odd: b0.mirror [-8 * k - 5, 2 * h - 10 * k - 9] | b3.value [2 * h - 10 * k - 7, 6 * k + 5 - 2 * h] | b4.mirror [6 * k + 7 - 2 * h, -1]
--   x ≤ 0, x even: b2.mirror [-8 * k - 4, -2 * k - 2] | b1.mirror [-2 * k, 0]

/-- The block-reversal family `F4` (l = 8k + 6, μ = 6k + 5, 4 blocks, target order `2031`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famF4 (k : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (2 * k + 1) (3 * k + 2) ∪
    row (3 * k + 2) (6 * k + 4) (2 * k + 2) ∪
    row (5 * k + 4) 0 (2 * k + 1) ∪
    row (7 * k + 5) (5 * k + 3) (k + 1)

/-- The family `F4` solves `SP(l, δ)` with `l = 8 * k + 6`, `δ = 3 * k + 3` (`μ = 6 * k + 5`) on its whole domain. -/
theorem famF4_sp (k : ℤ)
    (h1 : 0 ≤ k) :
    SP (8 * k + 6) (3 * k + 3) (famF4 k) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [famF4, image_union_fst, Finset.mem_union, mem_image_fst_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famF4, image_union_snd, Finset.mem_union, mem_image_snd_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famF4, image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc]
    constructor
    · intro hx
      omega
    · intro hx
      simp only [or_assoc]
      rcases le_or_gt 1 x with hs | hs <;> rcases Int.emod_two_eq x with hp | hp
      · rcases le_or_gt x (4 * k + 2) with c1 | c1 <;>
          repeat (first | (left; omega) | right | omega)
      · rcases le_or_gt x (2 * k + 1) with c1 | c1 <;>
          repeat (first | (left; omega) | right | omega)
      · rcases le_or_gt x (-2 * k - 2) with c1 | c1 <;>
          repeat (first | (left; omega) | right | omega)
      · rcases le_or_gt x (-4 * k - 3) with c1 | c1 <;>
          repeat (first | (left; omega) | right | omega)
  · unfold famF4
    exact (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le
      (card_row_le _ _ _) (card_row_le _ _ _)) (card_row_le _ _ _))
      (card_row_le _ _ _)).trans (by omega)
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 2 * k + 1, n = 3 * k + 2; value [2 * k + 3, 8 * k + 5]; mirror [-8 * k - 4, -2 * k - 2]; P
--   b1: a = 3 * k + 2, c = 6 * k + 4, n = 2 * k + 2; value [4 * k + 4, 8 * k + 6]; mirror [-8 * k - 5, -4 * k - 3]; P
--   b2: a = 5 * k + 4, c = 0, n = 2 * k + 1; value [-4 * k - 1, -1]; mirror [2, 4 * k + 2]; N
--   b3: a = 7 * k + 5, c = 5 * k + 3, n = k + 1; value [1, 2 * k + 1]; mirror [-2 * k, 0]; P
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b3.value [1, 2 * k + 1] | b0.value [2 * k + 3, 8 * k + 5]
--   x ≥ 1, x even: b2.mirror [2, 4 * k + 2] | b1.value [4 * k + 4, 8 * k + 6]
--   x ≤ 0, x odd: b1.mirror [-8 * k - 5, -4 * k - 3] | b2.value [-4 * k - 1, -1]
--   x ≤ 0, x even: b0.mirror [-8 * k - 4, -2 * k - 2] | b3.mirror [-2 * k, 0]

end L2
