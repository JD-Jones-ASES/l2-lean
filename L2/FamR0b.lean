import L2.SP

/-!
# Block-reversal families for `l ≡ 0 (mod 4)`, second part

The families `U5`, `U7`, `V`, `T` of order `l = 4q`. Each is a union of rows (block
reversals) whose sizes are affine in the parameters, and each solves `SP(l, δ)` on its whole
domain: the value runs and mirror runs of its rows tile `[1 − l, l]`.

Each proof is the family's class table, mechanised. Sources and targets: the blocks tile `[1, l]`
in source order and in target order. Values: split `x ∈ [1 − l, l]` by sign and parity; in each of
the four cases the class table lists a chain of runs (value runs and mirror runs of single blocks)
that abut with step two and cover the case, and the range of `x` is cut at the chain's boundaries so
that each piece is one run. A block whose runs cross zero (type `C`) appears in two chains. The class
table of each family follows its theorem as a comment.
-/

namespace L2

/-- The block-reversal family `U5` (l = 4q, μ = 8s + 5, 8 blocks, target order `47035162`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famU5 (q s : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (2 * q - 4 * s - 2) (2 * s + 1) ∪
    row (2 * s + 1) (4 * q - 4 * s - 3) (2 * s + 2) ∪
    row (4 * s + 3) (3 * q + s + 1) (q - s - 1) ∪
    row (q + 3 * s + 2) (2 * q - 2 * s - 1) (q - s - 1) ∪
    row (2 * q + 2 * s + 1) 0 1 ∪
    row (2 * q + 2 * s + 2) (3 * q - 3 * s - 2) (q - s - 1) ∪
    row (3 * q + s + 1) (4 * q - 2 * s - 1) (3 * s + 2 - q) ∪
    row (2 * q + 4 * s + 3) 1 (2 * q - 4 * s - 3)

/-- The family `U5` solves `SP(l, δ)` with `l = 4 * q`, `δ = 4 * s + 3` (`μ = 8 * s + 5`) on its whole domain. -/
theorem famU5_sp (q s : ℤ)
    (h1 : q ≤ 3 * s + 1) (h2 : 0 ≤ s) (h3 : 0 ≤ s) (h4 : 0 ≤ s) (h5 : 2 * s + 2 ≤ q) (h6 : s + 2 ≤ q)
    (h7 : s + 1 ≤ q) (h8 : s + 1 ≤ q) (h9 : s + 1 ≤ q) (h10 : s ≤ q) (h11 : 0 ≤ q + s + 1) :
    SP (4 * q) (4 * s + 3) (famU5 q s) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [famU5, image_union_fst, mem_image_fst_row, Finset.mem_union, Finset.mem_Icc, or_assoc]
    constructor
    · intro hx
      omega
    · intro hx
      rcases le_or_gt x (0 + (2 * s + 1)) with hc | hc
      · left; omega
      rcases le_or_gt x (2 * s + 1 + (2 * s + 2)) with hc | hc
      · (iterate 1 right); left; omega
      rcases le_or_gt x (4 * s + 3 + (q - s - 1)) with hc | hc
      · (iterate 2 right); left; omega
      rcases le_or_gt x (q + 3 * s + 2 + (q - s - 1)) with hc | hc
      · (iterate 3 right); left; omega
      rcases le_or_gt x (2 * q + 2 * s + 1 + (1)) with hc | hc
      · (iterate 4 right); left; omega
      rcases le_or_gt x (2 * q + 2 * s + 2 + (q - s - 1)) with hc | hc
      · (iterate 5 right); left; omega
      rcases le_or_gt x (3 * q + s + 1 + (3 * s + 2 - q)) with hc | hc
      · (iterate 6 right); left; omega
      (iterate 7 right); omega
  · ext x
    simp only [famU5, image_union_snd, mem_image_snd_row, Finset.mem_union, Finset.mem_Icc, or_assoc]
    constructor
    · intro hx
      omega
    · intro hx
      rcases le_or_gt x (0 + (1)) with hc | hc
      · (iterate 4 right); left; omega
      rcases le_or_gt x (1 + (2 * q - 4 * s - 3)) with hc | hc
      · (iterate 7 right); omega
      rcases le_or_gt x (2 * q - 4 * s - 2 + (2 * s + 1)) with hc | hc
      · left; omega
      rcases le_or_gt x (2 * q - 2 * s - 1 + (q - s - 1)) with hc | hc
      · (iterate 3 right); left; omega
      rcases le_or_gt x (3 * q - 3 * s - 2 + (q - s - 1)) with hc | hc
      · (iterate 5 right); left; omega
      rcases le_or_gt x (4 * q - 4 * s - 3 + (2 * s + 2)) with hc | hc
      · (iterate 1 right); left; omega
      rcases le_or_gt x (4 * q - 2 * s - 1 + (3 * s + 2 - q)) with hc | hc
      · (iterate 6 right); left; omega
      (iterate 2 right); left; omega
  · ext x
    simp only [famU5, image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc, or_assoc]
    constructor
    · intro hx
      omega
    · intro hx
      rcases Int.emod_two_eq x with hp | hp
      · rcases le_or_gt 1 x with hs | hs
        · -- x ≥ 1, x even
          rcases le_or_gt x (2 * q - 2 * s - 2) with hc | hc
          · (iterate 3 right); left; omega
          rcases le_or_gt x (4 * s + 2) with hc | hc
          · (iterate 6 right); left; omega
          rcases le_or_gt x (4 * q - 4 * s - 4) with hc | hc
          · (iterate 15 right); omega
          (iterate 1 right); left; omega
        · -- x ≤ 0, x even
          rcases le_or_gt x (-2 * q - 2 * s - 2) with hc | hc
          · (iterate 10 right); left; omega
          rcases le_or_gt x (2 * s - 2 * q) with hc | hc
          · (iterate 8 right); left; omega
          rcases le_or_gt x (2 * s + 2 - 2 * q) with hc | hc
          · (iterate 4 right); left; omega
          (iterate 13 right); left; omega
      · rcases le_or_gt 1 x with hs | hs
        · -- x ≥ 1, x odd
          rcases le_or_gt x (2 * q - 2 * s - 3) with hc | hc
          · (iterate 5 right); left; omega
          rcases le_or_gt x (2 * q - 2 * s - 1) with hc | hc
          · (iterate 12 right); left; omega
          rcases le_or_gt x (2 * q + 2 * s + 1) with hc | hc
          · left; omega
          (iterate 2 right); left; omega
        · -- x ≤ 0, x odd
          rcases le_or_gt x (4 * s + 3 - 4 * q) with hc | hc
          · (iterate 9 right); left; omega
          rcases le_or_gt x (-4 * s - 3) with hc | hc
          · (iterate 7 right); left; omega
          rcases le_or_gt x (2 * s + 1 - 2 * q) with hc | hc
          · (iterate 14 right); left; omega
          (iterate 11 right); left; omega
  · unfold famU5
    exact (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_row_le _ _ _) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)).trans (by omega)
-- The class table of `famU5`, the proof plan of `famU5_sp` above.
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 2 * q - 4 * s - 2, n = 2 * s + 1; value [2 * q + 1 - 2 * s, 2 * q + 2 * s + 1]; mirror [-2 * q - 2 * s, 2 * s - 2 * q]; P
--   b1: a = 2 * s + 1, c = 4 * q - 4 * s - 3, n = 2 * s + 2; value [4 * q - 4 * s - 2, 4 * q]; mirror [1 - 4 * q, 4 * s + 3 - 4 * q]; P
--   b2: a = 4 * s + 3, c = 3 * q + s + 1, n = q - s - 1; value [2 * q + 2 * s + 3, 4 * q - 1]; mirror [2 - 4 * q, -2 * q - 2 * s - 2]; P
--   b3: a = q + 3 * s + 2, c = 2 * q - 2 * s - 1, n = q - s - 1; value [2, 2 * q - 2 * s - 2]; mirror [2 * s + 3 - 2 * q, -1]; P
--   b4: a = 2 * q + 2 * s + 1, c = 0, n = 1; value [2 * s + 2 - 2 * q, 2 * s + 2 - 2 * q]; mirror [2 * q - 2 * s - 1, 2 * q - 2 * s - 1]; N
--   b5: a = 2 * q + 2 * s + 2, c = 3 * q - 3 * s - 2, n = q - s - 1; value [1, 2 * q - 2 * s - 3]; mirror [2 * s + 4 - 2 * q, 0]; P
--   b6: a = 3 * q + s + 1, c = 4 * q - 2 * s - 1, n = 3 * s + 2 - q; value [2 * q - 2 * s, 4 * s + 2]; mirror [-4 * s - 1, 2 * s + 1 - 2 * q]; P
--   b7: a = 2 * q + 4 * s + 3, c = 1, n = 2 * q - 4 * s - 3; value [4 * s + 5 - 4 * q, -4 * s - 3]; mirror [4 * s + 4, 4 * q - 4 * s - 4]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b5.value [1, 2 * q - 2 * s - 3] | b4.mirror [2 * q - 2 * s - 1, 2 * q - 2 * s - 1] | b0.value [2 * q + 1 - 2 * s, 2 * q + 2 * s + 1] | b2.value [2 * q + 2 * s + 3, 4 * q - 1]
--   x ≥ 1, x even: b3.value [2, 2 * q - 2 * s - 2] | b6.value [2 * q - 2 * s, 4 * s + 2] | b7.mirror [4 * s + 4, 4 * q - 4 * s - 4] | b1.value [4 * q - 4 * s - 2, 4 * q]
--   x ≤ 0, x odd: b1.mirror [1 - 4 * q, 4 * s + 3 - 4 * q] | b7.value [4 * s + 5 - 4 * q, -4 * s - 3] | b6.mirror [-4 * s - 1, 2 * s + 1 - 2 * q] | b3.mirror [2 * s + 3 - 2 * q, -1]
--   x ≤ 0, x even: b2.mirror [2 - 4 * q, -2 * q - 2 * s - 2] | b0.mirror [-2 * q - 2 * s, 2 * s - 2 * q] | b4.value [2 * s + 2 - 2 * q, 2 * s + 2 - 2 * q] | b5.mirror [2 * s + 4 - 2 * q, 0]

/-- The block-reversal family `U7` (l = 4q, μ = 8s + 7, 9 blocks, target order `162470835`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famU7 (q s : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (4 * q - 5 * s - 4) (s + 1) ∪
    row (s + 1) 0 (s + 1) ∪
    row (2 * s + 2) (4 * q - 7 * s - 6) (s + 1) ∪
    row (3 * s + 3) (2 * q + s + 1) (2 * q - 2 * s - 2) ∪
    row (2 * q + s + 1) (4 * q - 6 * s - 5) (5 * s + 4 - 2 * q) ∪
    row (6 * s + 5) (4 * q - s - 1) (s + 1) ∪
    row (7 * s + 6) (s + 1) (4 * q - 8 * s - 7) ∪
    row (4 * q - s - 1) (2 * q - s - 1) (2 * q - 4 * s - 3) ∪
    row (6 * q - 5 * s - 4) (4 * q - 4 * s - 3) (5 * s + 4 - 2 * q)

/-- The family `U7` solves `SP(l, δ)` with `l = 4 * q`, `δ = 4 * s + 4` (`μ = 8 * s + 7`) on its whole domain. -/
theorem famU7_sp (q s : ℤ)
    (h1 : 2 * q ≤ 5 * s + 3) (h2 : 2 * q ≤ 5 * s + 4) (h3 : 0 ≤ s) (h4 : 0 ≤ s + 1) (h5 : 2 * s + 2 ≤ q)
    (h6 : 2 * s + 2 ≤ q) (h7 : s + 2 ≤ q) (h8 : s + 1 ≤ q) (h9 : 3 * s + 3 ≤ 2 * q) (h10 : s + 1 ≤ 2 * q) :
    SP (4 * q) (4 * s + 4) (famU7 q s) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [famU7, image_union_fst, mem_image_fst_row, Finset.mem_union, Finset.mem_Icc, or_assoc]
    constructor
    · intro hx
      omega
    · intro hx
      rcases le_or_gt x (0 + (s + 1)) with hc | hc
      · left; omega
      rcases le_or_gt x (s + 1 + (s + 1)) with hc | hc
      · (iterate 1 right); left; omega
      rcases le_or_gt x (2 * s + 2 + (s + 1)) with hc | hc
      · (iterate 2 right); left; omega
      rcases le_or_gt x (3 * s + 3 + (2 * q - 2 * s - 2)) with hc | hc
      · (iterate 3 right); left; omega
      rcases le_or_gt x (2 * q + s + 1 + (5 * s + 4 - 2 * q)) with hc | hc
      · (iterate 4 right); left; omega
      rcases le_or_gt x (6 * s + 5 + (s + 1)) with hc | hc
      · (iterate 5 right); left; omega
      rcases le_or_gt x (7 * s + 6 + (4 * q - 8 * s - 7)) with hc | hc
      · (iterate 6 right); left; omega
      rcases le_or_gt x (4 * q - s - 1 + (2 * q - 4 * s - 3)) with hc | hc
      · (iterate 7 right); left; omega
      (iterate 8 right); omega
  · ext x
    simp only [famU7, image_union_snd, mem_image_snd_row, Finset.mem_union, Finset.mem_Icc, or_assoc]
    constructor
    · intro hx
      omega
    · intro hx
      rcases le_or_gt x (0 + (s + 1)) with hc | hc
      · (iterate 1 right); left; omega
      rcases le_or_gt x (s + 1 + (4 * q - 8 * s - 7)) with hc | hc
      · (iterate 6 right); left; omega
      rcases le_or_gt x (4 * q - 7 * s - 6 + (s + 1)) with hc | hc
      · (iterate 2 right); left; omega
      rcases le_or_gt x (4 * q - 6 * s - 5 + (5 * s + 4 - 2 * q)) with hc | hc
      · (iterate 4 right); left; omega
      rcases le_or_gt x (2 * q - s - 1 + (2 * q - 4 * s - 3)) with hc | hc
      · (iterate 7 right); left; omega
      rcases le_or_gt x (4 * q - 5 * s - 4 + (s + 1)) with hc | hc
      · left; omega
      rcases le_or_gt x (4 * q - 4 * s - 3 + (5 * s + 4 - 2 * q)) with hc | hc
      · (iterate 8 right); omega
      rcases le_or_gt x (2 * q + s + 1 + (2 * q - 2 * s - 2)) with hc | hc
      · (iterate 3 right); left; omega
      (iterate 5 right); left; omega
  · ext x
    simp only [famU7, image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc, or_assoc]
    constructor
    · intro hx
      omega
    · intro hx
      rcases Int.emod_two_eq x with hp | hp
      · rcases le_or_gt 1 x with hs | hs
        · -- x ≥ 1, x even
          rcases le_or_gt x (10 * s + 8 - 4 * q) with hc | hc
          · (iterate 8 right); left; omega
          rcases le_or_gt x (4 * q - 6 * s - 6) with hc | hc
          · (iterate 15 right); left; omega
          rcases le_or_gt x (4 * q - 4 * s - 4) with hc | hc
          · (iterate 2 right); left; omega
          rcases le_or_gt x (4 * q - 2 * s - 2) with hc | hc
          · (iterate 5 right); left; omega
          left; omega
        · -- x ≤ 0, x even
          rcases le_or_gt x (-4 * s - 4) with hc | hc
          · (iterate 12 right); left; omega
          rcases le_or_gt x (-2 * s - 2) with hc | hc
          · (iterate 10 right); left; omega
          rcases le_or_gt x (8 * s + 6 - 4 * q) with hc | hc
          · (iterate 13 right); left; omega
          (iterate 7 right); left; omega
      · rcases le_or_gt 1 x with hs | hs
        · -- x ≥ 1, x odd
          rcases le_or_gt x (4 * q - 8 * s - 7) with hc | hc
          · (iterate 16 right); left; omega
          rcases le_or_gt x (2 * s + 1) with hc | hc
          · (iterate 4 right); left; omega
          rcases le_or_gt x (4 * s + 3) with hc | hc
          · (iterate 1 right); left; omega
          (iterate 3 right); left; omega
        · -- x ≤ 0, x odd
          rcases le_or_gt x (2 * s + 1 - 4 * q) with hc | hc
          · (iterate 9 right); left; omega
          rcases le_or_gt x (4 * s + 3 - 4 * q) with hc | hc
          · (iterate 14 right); left; omega
          rcases le_or_gt x (6 * s + 5 - 4 * q) with hc | hc
          · (iterate 11 right); left; omega
          rcases le_or_gt x (4 * q - 10 * s - 9) with hc | hc
          · (iterate 6 right); left; omega
          (iterate 17 right); omega
  · unfold famU7
    exact (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_row_le _ _ _) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)).trans (by omega)
-- The class table of `famU7`, the proof plan of `famU7_sp` above.
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 4 * q - 5 * s - 4, n = s + 1; value [4 * q - 2 * s, 4 * q]; mirror [1 - 4 * q, 2 * s + 1 - 4 * q]; P
--   b1: a = s + 1, c = 0, n = s + 1; value [2 * s + 3, 4 * s + 3]; mirror [-4 * s - 2, -2 * s - 2]; P
--   b2: a = 2 * s + 2, c = 4 * q - 7 * s - 6, n = s + 1; value [4 * q - 6 * s - 4, 4 * q - 4 * s - 4]; mirror [4 * s + 5 - 4 * q, 6 * s + 5 - 4 * q]; P
--   b3: a = 3 * s + 3, c = 2 * q + s + 1, n = 2 * q - 2 * s - 2; value [4 * s + 5, 4 * q - 1]; mirror [2 - 4 * q, -4 * s - 4]; P
--   b4: a = 2 * q + s + 1, c = 4 * q - 6 * s - 5, n = 5 * s + 4 - 2 * q; value [4 * q - 8 * s - 5, 2 * s + 1]; mirror [-2 * s, 8 * s + 6 - 4 * q]; P
--   b5: a = 6 * s + 5, c = 4 * q - s - 1, n = s + 1; value [4 * q - 4 * s - 2, 4 * q - 2 * s - 2]; mirror [2 * s + 3 - 4 * q, 4 * s + 3 - 4 * q]; P
--   b6: a = 7 * s + 6, c = s + 1, n = 4 * q - 8 * s - 7; value [6 * s + 7 - 4 * q, 4 * q - 10 * s - 9]; mirror [10 * s + 10 - 4 * q, 4 * q - 6 * s - 6]; N
--   b7: a = 4 * q - s - 1, c = 2 * q - s - 1, n = 2 * q - 4 * s - 3; value [8 * s + 8 - 4 * q, 0]; mirror [1, 4 * q - 8 * s - 7]; N
--   b8: a = 6 * q - 5 * s - 4, c = 4 * q - 4 * s - 3, n = 5 * s + 4 - 2 * q; value [2, 10 * s + 8 - 4 * q]; mirror [4 * q - 10 * s - 7, -1]; P
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b7.mirror [1, 4 * q - 8 * s - 7] | b4.value [4 * q - 8 * s - 5, 2 * s + 1] | b1.value [2 * s + 3, 4 * s + 3] | b3.value [4 * s + 5, 4 * q - 1]
--   x ≥ 1, x even: b8.value [2, 10 * s + 8 - 4 * q] | b6.mirror [10 * s + 10 - 4 * q, 4 * q - 6 * s - 6] | b2.value [4 * q - 6 * s - 4, 4 * q - 4 * s - 4] | b5.value [4 * q - 4 * s - 2, 4 * q - 2 * s - 2] | b0.value [4 * q - 2 * s, 4 * q]
--   x ≤ 0, x odd: b0.mirror [1 - 4 * q, 2 * s + 1 - 4 * q] | b5.mirror [2 * s + 3 - 4 * q, 4 * s + 3 - 4 * q] | b2.mirror [4 * s + 5 - 4 * q, 6 * s + 5 - 4 * q] | b6.value [6 * s + 7 - 4 * q, 4 * q - 10 * s - 9] | b8.mirror [4 * q - 10 * s - 7, -1]
--   x ≤ 0, x even: b3.mirror [2 - 4 * q, -4 * s - 4] | b1.mirror [-4 * s - 2, -2 * s - 2] | b4.mirror [-2 * s, 8 * s + 6 - 4 * q] | b7.value [8 * s + 8 - 4 * q, 0]

/-- The block-reversal family `V` (l = 4q, μ = 4s + 3, 9 blocks, target order `805734126`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famV (q s : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (q - s - 1) (q - s) ∪
    row (q - s) (5 * q - 4 * s - 2) s ∪
    row q (5 * q - 3 * s - 2) (s + 1) ∪
    row (q + s + 1) (3 * q - 2 * s - 1) (4 * q - 5 * s - 2) ∪
    row (5 * q - 4 * s - 1) (7 * q - 7 * s - 3) (3 * s + 1 - 2 * q) ∪
    row (3 * q - s) (2 * q - 2 * s - 1) (5 * s + 2 - 3 * q) ∪
    row (4 * s + 2) (5 * q - 2 * s - 1) (2 * s + 1 - q) ∪
    row (6 * s + 3 - q) (3 * s + 1 - q) (4 * q - 5 * s - 2) ∪
    row (3 * q + s + 1) 0 (q - s - 1)

/-- The family `V` solves `SP(l, δ)` with `l = 4 * q`, `δ = 2 * s + 2` (`μ = 4 * s + 3`) on its whole domain. -/
theorem famV_sp (q s : ℤ)
    (h1 : 3 * q ≤ 5 * s + 1) (h2 : 2 * q ≤ 3 * s) (h3 : 2 * q ≤ 3 * s) (h4 : 2 * q ≤ 3 * s + 1)
    (h5 : q ≤ 2 * s) (h6 : q ≤ 2 * s + 1) (h7 : 1 ≤ s) (h8 : 0 ≤ s) (h9 : 0 ≤ s) (h10 : s + 2 ≤ q)
    (h11 : s + 1 ≤ q) (h12 : s + 1 ≤ q) (h13 : 0 ≤ q) (h14 : s + 1 ≤ 2 * q) (h15 : s ≤ 2 * q)
    (h16 : s + 1 ≤ q) (h17 : 5 * s + 3 ≤ 4 * q) :
    SP (4 * q) (2 * s + 2) (famV q s) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [famV, image_union_fst, mem_image_fst_row, Finset.mem_union, Finset.mem_Icc, or_assoc]
    constructor
    · intro hx
      omega
    · intro hx
      rcases le_or_gt x (0 + (q - s)) with hc | hc
      · left; omega
      rcases le_or_gt x (q - s + (s)) with hc | hc
      · (iterate 1 right); left; omega
      rcases le_or_gt x (q + (s + 1)) with hc | hc
      · (iterate 2 right); left; omega
      rcases le_or_gt x (q + s + 1 + (4 * q - 5 * s - 2)) with hc | hc
      · (iterate 3 right); left; omega
      rcases le_or_gt x (5 * q - 4 * s - 1 + (3 * s + 1 - 2 * q)) with hc | hc
      · (iterate 4 right); left; omega
      rcases le_or_gt x (3 * q - s + (5 * s + 2 - 3 * q)) with hc | hc
      · (iterate 5 right); left; omega
      rcases le_or_gt x (4 * s + 2 + (2 * s + 1 - q)) with hc | hc
      · (iterate 6 right); left; omega
      rcases le_or_gt x (6 * s + 3 - q + (4 * q - 5 * s - 2)) with hc | hc
      · (iterate 7 right); left; omega
      (iterate 8 right); omega
  · ext x
    simp only [famV, image_union_snd, mem_image_snd_row, Finset.mem_union, Finset.mem_Icc, or_assoc]
    constructor
    · intro hx
      omega
    · intro hx
      rcases le_or_gt x (0 + (q - s - 1)) with hc | hc
      · (iterate 8 right); omega
      rcases le_or_gt x (q - s - 1 + (q - s)) with hc | hc
      · left; omega
      rcases le_or_gt x (2 * q - 2 * s - 1 + (5 * s + 2 - 3 * q)) with hc | hc
      · (iterate 5 right); left; omega
      rcases le_or_gt x (3 * s + 1 - q + (4 * q - 5 * s - 2)) with hc | hc
      · (iterate 7 right); left; omega
      rcases le_or_gt x (3 * q - 2 * s - 1 + (4 * q - 5 * s - 2)) with hc | hc
      · (iterate 3 right); left; omega
      rcases le_or_gt x (7 * q - 7 * s - 3 + (3 * s + 1 - 2 * q)) with hc | hc
      · (iterate 4 right); left; omega
      rcases le_or_gt x (5 * q - 4 * s - 2 + (s)) with hc | hc
      · (iterate 1 right); left; omega
      rcases le_or_gt x (5 * q - 3 * s - 2 + (s + 1)) with hc | hc
      · (iterate 2 right); left; omega
      (iterate 6 right); left; omega
  · ext x
    simp only [famV, image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc, or_assoc]
    constructor
    · intro hx
      omega
    · intro hx
      rcases Int.emod_two_eq x with hp | hp
      · rcases le_or_gt 1 x with hs | hs
        · -- x ≥ 1, x even
          rcases le_or_gt x (6 * s + 2 - 4 * q) with hc | hc
          · (iterate 5 right); left; omega
          rcases le_or_gt x (4 * q - 4 * s - 2) with hc | hc
          · (iterate 16 right); left; omega
          rcases le_or_gt x (2 * s) with hc | hc
          · (iterate 4 right); left; omega
          rcases le_or_gt x (2 * q) with hc | hc
          · left; omega
          rcases le_or_gt x (4 * q - 2 * s - 2) with hc | hc
          · (iterate 17 right); omega
          (iterate 2 right); left; omega
        · -- x ≤ 0, x even
          rcases le_or_gt x (2 * s - 4 * q) with hc | hc
          · (iterate 10 right); left; omega
          rcases le_or_gt x (6 * s + 2 - 6 * q) with hc | hc
          · (iterate 15 right); left; omega
          rcases le_or_gt x (2 * q - 4 * s - 2) with hc | hc
          · (iterate 12 right); left; omega
          (iterate 5 right); left; omega
      · rcases le_or_gt 1 x with hs | hs
        · -- x ≥ 1, x odd
          rcases le_or_gt x (4 * s + 1 - 2 * q) with hc | hc
          · (iterate 14 right); left; omega
          rcases le_or_gt x (6 * q - 6 * s - 3) with hc | hc
          · (iterate 3 right); left; omega
          rcases le_or_gt x (4 * q - 2 * s - 1) with hc | hc
          · (iterate 6 right); left; omega
          (iterate 1 right); left; omega
        · -- x ≤ 0, x odd
          rcases le_or_gt x (2 * s + 1 - 4 * q) with hc | hc
          · (iterate 11 right); left; omega
          rcases le_or_gt x (-2 * q - 1) with hc | hc
          · (iterate 8 right); left; omega
          rcases le_or_gt x (-2 * s - 1) with hc | hc
          · (iterate 9 right); left; omega
          rcases le_or_gt x (4 * s + 1 - 4 * q) with hc | hc
          · (iterate 13 right); left; omega
          rcases le_or_gt x (4 * q - 6 * s - 3) with hc | hc
          · (iterate 7 right); left; omega
          (iterate 14 right); left; omega
  · unfold famV
    exact (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_row_le _ _ _) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)).trans (by omega)
-- The class table of `famV`, the proof plan of `famV_sp` above.
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = q - s - 1, n = q - s; value [2 * s + 2, 2 * q]; mirror [1 - 2 * q, -2 * s - 1]; P
--   b1: a = q - s, c = 5 * q - 4 * s - 2, n = s; value [4 * q + 1 - 2 * s, 4 * q - 1]; mirror [2 - 4 * q, 2 * s - 4 * q]; P
--   b2: a = q, c = 5 * q - 3 * s - 2, n = s + 1; value [4 * q - 2 * s, 4 * q]; mirror [1 - 4 * q, 2 * s + 1 - 4 * q]; P
--   b3: a = q + s + 1, c = 3 * q - 2 * s - 1, n = 4 * q - 5 * s - 2; value [4 * s + 3 - 2 * q, 6 * q - 6 * s - 3]; mirror [6 * s + 4 - 6 * q, 2 * q - 4 * s - 2]; P
--   b4: a = 5 * q - 4 * s - 1, c = 7 * q - 7 * s - 3, n = 3 * s + 1 - 2 * q; value [4 * q - 4 * s, 2 * s]; mirror [1 - 2 * s, 4 * s + 1 - 4 * q]; P
--   b5: a = 3 * q - s, c = 2 * q - 2 * s - 1, n = 5 * s + 2 - 3 * q; value [2 * q - 4 * s, 6 * s + 2 - 4 * q]; mirror [4 * q - 6 * s - 1, 4 * s + 1 - 2 * q]; C
--   b6: a = 4 * s + 2, c = 5 * q - 2 * s - 1, n = 2 * s + 1 - q; value [6 * q - 6 * s - 1, 4 * q - 2 * s - 1]; mirror [2 * s + 2 - 4 * q, 6 * s + 2 - 6 * q]; P
--   b7: a = 6 * s + 3 - q, c = 3 * s + 1 - q, n = 4 * q - 5 * s - 2; value [4 * s + 3 - 4 * q, 4 * q - 6 * s - 3]; mirror [6 * s + 4 - 4 * q, 4 * q - 4 * s - 2]; N
--   b8: a = 3 * q + s + 1, c = 0, n = q - s - 1; value [2 * s + 3 - 4 * q, -2 * q - 1]; mirror [2 * q + 2, 4 * q - 2 * s - 2]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b5.mirror [1, 4 * s + 1 - 2 * q] | b3.value [4 * s + 3 - 2 * q, 6 * q - 6 * s - 3] | b6.value [6 * q - 6 * s - 1, 4 * q - 2 * s - 1] | b1.value [4 * q + 1 - 2 * s, 4 * q - 1]
--   x ≥ 1, x even: b5.value [2, 6 * s + 2 - 4 * q] | b7.mirror [6 * s + 4 - 4 * q, 4 * q - 4 * s - 2] | b4.value [4 * q - 4 * s, 2 * s] | b0.value [2 * s + 2, 2 * q] | b8.mirror [2 * q + 2, 4 * q - 2 * s - 2] | b2.value [4 * q - 2 * s, 4 * q]
--   x ≤ 0, x odd: b2.mirror [1 - 4 * q, 2 * s + 1 - 4 * q] | b8.value [2 * s + 3 - 4 * q, -2 * q - 1] | b0.mirror [1 - 2 * q, -2 * s - 1] | b4.mirror [1 - 2 * s, 4 * s + 1 - 4 * q] | b7.value [4 * s + 3 - 4 * q, 4 * q - 6 * s - 3] | b5.mirror [4 * q - 6 * s - 1, -1]
--   x ≤ 0, x even: b1.mirror [2 - 4 * q, 2 * s - 4 * q] | b6.mirror [2 * s + 2 - 4 * q, 6 * s + 2 - 6 * q] | b3.mirror [6 * s + 4 - 6 * q, 2 * q - 4 * s - 2] | b5.value [2 * q - 4 * s, 0]

/-- The block-reversal family `T` (l = 4q, μ = 8s + 3, 7 blocks, target order `2360415`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famT (q s : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (4 * q - 6 * s - 2) (2 * s + 1) ∪
    row (2 * s + 1) (4 * q - 3 * s - 1) s ∪
    row (3 * s + 1) 0 (4 * q - 7 * s - 2) ∪
    row (4 * q - 4 * s - 1) (4 * q - 7 * s - 2) (9 * s + 3 - 4 * q) ∪
    row (5 * s + 2) (4 * q - 4 * s - 1) s ∪
    row (6 * s + 2) (4 * q - 2 * s - 1) (2 * s + 1) ∪
    row (8 * s + 3) (2 * s + 1) (4 * q - 8 * s - 3)

/-- The family `T` solves `SP(l, δ)` with `l = 4 * q`, `δ = 4 * s + 2` (`μ = 8 * s + 3`) on its whole domain. -/
theorem famT_sp (q s : ℤ)
    (h1 : 4 * q ≤ 9 * s + 2) (h2 : 2 * q ≤ 5 * s + 2) (h3 : 1 ≤ s) (h4 : 0 ≤ s) (h5 : 2 * s + 1 ≤ q)
    (h6 : 2 * s + 1 ≤ q) (h7 : s + 1 ≤ q) (h8 : 3 * s + 2 ≤ 2 * q) (h9 : 3 * s + 1 ≤ 2 * q)
    (h10 : 3 * s + 1 ≤ 2 * q) (h11 : s ≤ 2 * q) (h12 : 7 * s + 3 ≤ 4 * q) :
    SP (4 * q) (4 * s + 2) (famT q s) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [famT, image_union_fst, mem_image_fst_row, Finset.mem_union, Finset.mem_Icc, or_assoc]
    constructor
    · intro hx
      omega
    · intro hx
      rcases le_or_gt x (0 + (2 * s + 1)) with hc | hc
      · left; omega
      rcases le_or_gt x (2 * s + 1 + (s)) with hc | hc
      · (iterate 1 right); left; omega
      rcases le_or_gt x (3 * s + 1 + (4 * q - 7 * s - 2)) with hc | hc
      · (iterate 2 right); left; omega
      rcases le_or_gt x (4 * q - 4 * s - 1 + (9 * s + 3 - 4 * q)) with hc | hc
      · (iterate 3 right); left; omega
      rcases le_or_gt x (5 * s + 2 + (s)) with hc | hc
      · (iterate 4 right); left; omega
      rcases le_or_gt x (6 * s + 2 + (2 * s + 1)) with hc | hc
      · (iterate 5 right); left; omega
      (iterate 6 right); omega
  · ext x
    simp only [famT, image_union_snd, mem_image_snd_row, Finset.mem_union, Finset.mem_Icc, or_assoc]
    constructor
    · intro hx
      omega
    · intro hx
      rcases le_or_gt x (0 + (4 * q - 7 * s - 2)) with hc | hc
      · (iterate 2 right); left; omega
      rcases le_or_gt x (4 * q - 7 * s - 2 + (9 * s + 3 - 4 * q)) with hc | hc
      · (iterate 3 right); left; omega
      rcases le_or_gt x (2 * s + 1 + (4 * q - 8 * s - 3)) with hc | hc
      · (iterate 6 right); omega
      rcases le_or_gt x (4 * q - 6 * s - 2 + (2 * s + 1)) with hc | hc
      · left; omega
      rcases le_or_gt x (4 * q - 4 * s - 1 + (s)) with hc | hc
      · (iterate 4 right); left; omega
      rcases le_or_gt x (4 * q - 3 * s - 1 + (s)) with hc | hc
      · (iterate 1 right); left; omega
      (iterate 5 right); left; omega
  · ext x
    simp only [famT, image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc, or_assoc]
    constructor
    · intro hx
      omega
    · intro hx
      rcases Int.emod_two_eq x with hp | hp
      · rcases le_or_gt 1 x with hs | hs
        · -- x ≥ 1, x even
          rcases le_or_gt x (4 * q - 6 * s - 2) with hc | hc
          · (iterate 2 right); left; omega
          rcases le_or_gt x (4 * q - 4 * s - 2) with hc | hc
          · (iterate 4 right); left; omega
          left; omega
        · -- x ≤ 0, x even
          rcases le_or_gt x (2 * s - 4 * q) with hc | hc
          · (iterate 8 right); left; omega
          rcases le_or_gt x (6 * s + 2 - 4 * q) with hc | hc
          · (iterate 12 right); left; omega
          rcases le_or_gt x (4 * q - 10 * s - 4) with hc | hc
          · (iterate 6 right); left; omega
          rcases le_or_gt x (8 * s + 2 - 4 * q) with hc | hc
          · (iterate 10 right); left; omega
          (iterate 2 right); left; omega
      · rcases le_or_gt 1 x with hs | hs
        · -- x ≥ 1, x odd
          rcases le_or_gt x (4 * q - 8 * s - 3) with hc | hc
          · (iterate 9 right); left; omega
          rcases le_or_gt x (10 * s + 3 - 4 * q) with hc | hc
          · (iterate 3 right); left; omega
          rcases le_or_gt x (4 * q - 6 * s - 3) with hc | hc
          · (iterate 13 right); omega
          rcases le_or_gt x (4 * q - 2 * s - 1) with hc | hc
          · (iterate 5 right); left; omega
          (iterate 1 right); left; omega
        · -- x ≤ 0, x odd
          rcases le_or_gt x (4 * s + 1 - 4 * q) with hc | hc
          · (iterate 7 right); left; omega
          rcases le_or_gt x (6 * s + 1 - 4 * q) with hc | hc
          · (iterate 11 right); left; omega
          (iterate 9 right); left; omega
  · unfold famT
    exact (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_row_le _ _ _) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)).trans (by omega)
-- The class table of `famT`, the proof plan of `famT_sp` above.
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 4 * q - 6 * s - 2, n = 2 * s + 1; value [4 * q - 4 * s, 4 * q]; mirror [1 - 4 * q, 4 * s + 1 - 4 * q]; P
--   b1: a = 2 * s + 1, c = 4 * q - 3 * s - 1, n = s; value [4 * q + 1 - 2 * s, 4 * q - 1]; mirror [2 - 4 * q, 2 * s - 4 * q]; P
--   b2: a = 3 * s + 1, c = 0, n = 4 * q - 7 * s - 2; value [8 * s + 4 - 4 * q, 4 * q - 6 * s - 2]; mirror [6 * s + 3 - 4 * q, 4 * q - 8 * s - 3]; C
--   b3: a = 4 * q - 4 * s - 1, c = 4 * q - 7 * s - 2, n = 9 * s + 3 - 4 * q; value [4 * q - 8 * s - 1, 10 * s + 3 - 4 * q]; mirror [4 * q - 10 * s - 2, 8 * s + 2 - 4 * q]; P
--   b4: a = 5 * s + 2, c = 4 * q - 4 * s - 1, n = s; value [4 * q - 6 * s, 4 * q - 4 * s - 2]; mirror [4 * s + 3 - 4 * q, 6 * s + 1 - 4 * q]; P
--   b5: a = 6 * s + 2, c = 4 * q - 2 * s - 1, n = 2 * s + 1; value [4 * q - 6 * s - 1, 4 * q - 2 * s - 1]; mirror [2 * s + 2 - 4 * q, 6 * s + 2 - 4 * q]; P
--   b6: a = 8 * s + 3, c = 2 * s + 1, n = 4 * q - 8 * s - 3; value [6 * s + 4 - 4 * q, 4 * q - 10 * s - 4]; mirror [10 * s + 5 - 4 * q, 4 * q - 6 * s - 3]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b2.mirror [1, 4 * q - 8 * s - 3] | b3.value [4 * q - 8 * s - 1, 10 * s + 3 - 4 * q] | b6.mirror [10 * s + 5 - 4 * q, 4 * q - 6 * s - 3] | b5.value [4 * q - 6 * s - 1, 4 * q - 2 * s - 1] | b1.value [4 * q + 1 - 2 * s, 4 * q - 1]
--   x ≥ 1, x even: b2.value [2, 4 * q - 6 * s - 2] | b4.value [4 * q - 6 * s, 4 * q - 4 * s - 2] | b0.value [4 * q - 4 * s, 4 * q]
--   x ≤ 0, x odd: b0.mirror [1 - 4 * q, 4 * s + 1 - 4 * q] | b4.mirror [4 * s + 3 - 4 * q, 6 * s + 1 - 4 * q] | b2.mirror [6 * s + 3 - 4 * q, -1]
--   x ≤ 0, x even: b1.mirror [2 - 4 * q, 2 * s - 4 * q] | b5.mirror [2 * s + 2 - 4 * q, 6 * s + 2 - 4 * q] | b6.value [6 * s + 4 - 4 * q, 4 * q - 10 * s - 4] | b3.mirror [4 * q - 10 * s - 2, 8 * s + 2 - 4 * q] | b2.value [8 * s + 4 - 4 * q, 0]

end L2
