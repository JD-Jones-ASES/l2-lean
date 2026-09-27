import L2.SP

/-!
# Block-reversal families for `l ≡ 3 (mod 4)`

The families `R3O`, `R3E`, `R3Q`, `R3T1`, indexed by `t = (l − μ)/2`. Each is a union of rows
(block reversals) whose sizes are affine in the parameters, and each solves `SP(l, δ)` on its
whole domain: the value runs and mirror runs of its rows tile `[1 − l, l]`.

The proof of each family is its class table. Every row contributes a value run and a mirror run,
both of step two. For each parity of `x`, the runs of that parity, taken in increasing order, abut
with step two and cover `[1 − l, l]`; the table under each theorem lists them. The covering
direction of `values` splits `x` by parity and then at the boundaries of that chain, and in each
piece the run holding `x` is found by `omega`.
-/

namespace L2

/-- Close a goal `P₀ ∨ P₁ ∨ … ∨ Pₖ` of linear facts by the first disjunct that `omega` proves. -/
local macro "pick_run" : tactic =>
  `(tactic| ((repeat (first | exact Or.inl (by omega) | refine Or.inr ?_)) <;> omega))

/-- The block-reversal family `R3O` (l = 4q + 3, μ = l - 2t, t = 2u + 1, 7 blocks, target order `6134052`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famR3O (q u : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (q + 3 * u + 2) (q - u) ∪
    row (q - u) (2 * u + 1) (q - u) ∪
    row (2 * q - 2 * u) (3 * q + 2) (q + 1) ∪
    row (3 * q + 1 - 2 * u) (q + u + 1) u ∪
    row (3 * q + 1 - u) (q + 2 * u + 1) (u + 1) ∪
    row (3 * q + 2) (2 * q + 2 * u + 2) (q - 2 * u) ∪
    row (4 * q + 2 - 2 * u) 0 (2 * u + 1)

/-- The family `R3O` solves `SP(l, δ)` with `l = 4 * q + 3`, `δ = 2 * q + 1 - 2 * u` (`μ = 4 * q + 1 - 4 * u`) on its whole domain. -/
theorem famR3O_sp (q u : ℤ)
    (h1 : 1 ≤ u) (h2 : 2 * u + 1 ≤ q) :
    SP (4 * q + 3) (2 * q + 1 - 2 * u) (famR3O q u) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [famR3O, image_union_fst, Finset.mem_union, mem_image_fst_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famR3O, image_union_snd, Finset.mem_union, mem_image_snd_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famR3O, image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc, or_assoc]
    constructor
    · intro h
      omega
    · intro hx
      rcases Int.emod_two_eq x with hp | hp
      · rcases le_or_gt x (-2 * q - 2) with c | c
        · pick_run
        rcases le_or_gt x (-2 * u - 2) with c | c
        · pick_run
        rcases le_or_gt x 0 with c | c
        · pick_run
        rcases le_or_gt x (2 * u) with c | c
        · pick_run
        rcases le_or_gt x (2 * q - 2 * u) with c | c
        · pick_run
        rcases le_or_gt x (2 * q + 2 * u + 2) with c | c
        · pick_run
        pick_run
      · rcases le_or_gt x (-2 * q - 2 * u - 3) with c | c
        · pick_run
        rcases le_or_gt x (2 * u - 2 * q - 1) with c | c
        · pick_run
        rcases le_or_gt x (-2 * u - 1) with c | c
        · pick_run
        rcases le_or_gt x (-1) with c | c
        · pick_run
        rcases le_or_gt x (2 * u + 1) with c | c
        · pick_run
        rcases le_or_gt x (2 * q + 1) with c | c
        · pick_run
        pick_run
  · unfold famR3O
    exact (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le
      (card_union_le_of_le (card_union_le_of_le (card_row_le _ _ _) (card_row_le _ _ _))
      (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _))
      (card_row_le _ _ _)).trans (by omega)
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = q + 3 * u + 2, n = q - u; value [2 * q + 2 * u + 4, 4 * q + 2]; mirror [-4 * q - 1, -2 * q - 2 * u - 3]; P
--   b1: a = q - u, c = 2 * u + 1, n = q - u; value [2 * u + 3, 2 * q + 1]; mirror [-2 * q, -2 * u - 2]; P
--   b2: a = 2 * q - 2 * u, c = 3 * q + 2, n = q + 1; value [2 * q + 3, 4 * q + 3]; mirror [-4 * q - 2, -2 * q - 2]; P
--   b3: a = 3 * q + 1 - 2 * u, c = q + u + 1, n = u; value [2, 2 * u]; mirror [1 - 2 * u, -1]; P
--   b4: a = 3 * q + 1 - u, c = q + 2 * u + 1, n = u + 1; value [1, 2 * u + 1]; mirror [-2 * u, 0]; P
--   b5: a = 3 * q + 2, c = 2 * q + 2 * u + 2, n = q - 2 * u; value [2 * u + 2, 2 * q - 2 * u]; mirror [2 * u + 1 - 2 * q, -2 * u - 1]; P
--   b6: a = 4 * q + 2 - 2 * u, c = 0, n = 2 * u + 1; value [-2 * q - 2 * u - 1, 2 * u - 2 * q - 1]; mirror [2 * q + 2 - 2 * u, 2 * q + 2 * u + 2]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b4.value [1, 2 * u + 1] | b1.value [2 * u + 3, 2 * q + 1] | b2.value [2 * q + 3, 4 * q + 3]
--   x ≥ 1, x even: b3.value [2, 2 * u] | b5.value [2 * u + 2, 2 * q - 2 * u] | b6.mirror [2 * q + 2 - 2 * u, 2 * q + 2 * u + 2] | b0.value [2 * q + 2 * u + 4, 4 * q + 2]
--   x ≤ 0, x odd: b0.mirror [-4 * q - 1, -2 * q - 2 * u - 3] | b6.value [-2 * q - 2 * u - 1, 2 * u - 2 * q - 1] | b5.mirror [2 * u + 1 - 2 * q, -2 * u - 1] | b3.mirror [1 - 2 * u, -1]
--   x ≤ 0, x even: b2.mirror [-4 * q - 2, -2 * q - 2] | b1.mirror [-2 * q, -2 * u - 2] | b4.mirror [-2 * u, 0]

/-- The block-reversal family `R3E` (l = 4q + 3, μ = l - 2t, t = 2u, 8 blocks, target order `70245163`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famR3E (q u : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (2 * u) 1 ∪
    row 1 (q + 3 * u + 2) (q + 1 - u) ∪
    row (q + 2 - u) (2 * u + 1) (q - u) ∪
    row (2 * q + 2 - 2 * u) (3 * q + 3) q ∪
    row (3 * q + 2 - 2 * u) (q + u + 1) u ∪
    row (3 * q + 2 - u) (q + 2 * u + 1) (u + 1) ∪
    row (3 * q + 3) (2 * q + 2 * u + 3) (q - 2 * u) ∪
    row (4 * q + 3 - 2 * u) 0 (2 * u)

/-- The family `R3E` solves `SP(l, δ)` with `l = 4 * q + 3`, `δ = 2 * q + 2 - 2 * u` (`μ = 4 * q + 3 - 4 * u`) on its whole domain. -/
theorem famR3E_sp (q u : ℤ)
    (h1 : 1 ≤ u) (h2 : 2 * u + 1 ≤ q) :
    SP (4 * q + 3) (2 * q + 2 - 2 * u) (famR3E q u) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [famR3E, image_union_fst, Finset.mem_union, mem_image_fst_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famR3E, image_union_snd, Finset.mem_union, mem_image_snd_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famR3E, image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc, or_assoc]
    constructor
    · intro h
      omega
    · intro hx
      rcases Int.emod_two_eq x with hp | hp
      · rcases le_or_gt x (-2 * q - 2 * u - 2) with c | c
        · pick_run
        rcases le_or_gt x (2 * u - 2 * q - 2) with c | c
        · pick_run
        rcases le_or_gt x (-2 * u - 2) with c | c
        · pick_run
        rcases le_or_gt x 0 with c | c
        · pick_run
        rcases le_or_gt x (2 * u) with c | c
        · pick_run
        rcases le_or_gt x (2 * q) with c | c
        · pick_run
        rcases le_or_gt x (2 * q + 2) with c | c
        · pick_run
        pick_run
      · rcases le_or_gt x (-2 * q - 3) with c | c
        · pick_run
        rcases le_or_gt x (-2 * q - 1) with c | c
        · pick_run
        rcases le_or_gt x (-2 * u - 1) with c | c
        · pick_run
        rcases le_or_gt x (-1) with c | c
        · pick_run
        rcases le_or_gt x (2 * u + 1) with c | c
        · pick_run
        rcases le_or_gt x (2 * q + 1 - 2 * u) with c | c
        · pick_run
        rcases le_or_gt x (2 * q + 2 * u + 1) with c | c
        · pick_run
        pick_run
  · unfold famR3E
    exact (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le
      (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_row_le _ _ _)
      (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _))
      (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)).trans (by omega)
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 2 * u, n = 1; value [2 * q + 2, 2 * q + 2]; mirror [-2 * q - 1, -2 * q - 1]; P
--   b1: a = 1, c = q + 3 * u + 2, n = q + 1 - u; value [2 * q + 2 * u + 3, 4 * q + 3]; mirror [-4 * q - 2, -2 * q - 2 * u - 2]; P
--   b2: a = q + 2 - u, c = 2 * u + 1, n = q - u; value [2 * u + 2, 2 * q]; mirror [1 - 2 * q, -2 * u - 1]; P
--   b3: a = 2 * q + 2 - 2 * u, c = 3 * q + 3, n = q; value [2 * q + 4, 4 * q + 2]; mirror [-4 * q - 1, -2 * q - 3]; P
--   b4: a = 3 * q + 2 - 2 * u, c = q + u + 1, n = u; value [2, 2 * u]; mirror [1 - 2 * u, -1]; P
--   b5: a = 3 * q + 2 - u, c = q + 2 * u + 1, n = u + 1; value [1, 2 * u + 1]; mirror [-2 * u, 0]; P
--   b6: a = 3 * q + 3, c = 2 * q + 2 * u + 3, n = q - 2 * u; value [2 * u + 3, 2 * q + 1 - 2 * u]; mirror [2 * u - 2 * q, -2 * u - 2]; P
--   b7: a = 4 * q + 3 - 2 * u, c = 0, n = 2 * u; value [-2 * q - 2 * u, 2 * u - 2 * q - 2]; mirror [2 * q + 3 - 2 * u, 2 * q + 2 * u + 1]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b5.value [1, 2 * u + 1] | b6.value [2 * u + 3, 2 * q + 1 - 2 * u] | b7.mirror [2 * q + 3 - 2 * u, 2 * q + 2 * u + 1] | b1.value [2 * q + 2 * u + 3, 4 * q + 3]
--   x ≥ 1, x even: b4.value [2, 2 * u] | b2.value [2 * u + 2, 2 * q] | b0.value [2 * q + 2, 2 * q + 2] | b3.value [2 * q + 4, 4 * q + 2]
--   x ≤ 0, x odd: b3.mirror [-4 * q - 1, -2 * q - 3] | b0.mirror [-2 * q - 1, -2 * q - 1] | b2.mirror [1 - 2 * q, -2 * u - 1] | b4.mirror [1 - 2 * u, -1]
--   x ≤ 0, x even: b1.mirror [-4 * q - 2, -2 * q - 2 * u - 2] | b7.value [-2 * q - 2 * u, 2 * u - 2 * q - 2] | b6.mirror [2 * u - 2 * q, -2 * u - 2] | b5.mirror [-2 * u, 0]

/-- The block-reversal family `R3Q` (l = 4q + 3, μ = l - 2t, t = 2u, 7 blocks, target order `6024513`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famR3Q (q u : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (2 * u) (2 * q + 1 - 4 * u) ∪
    row (2 * q + 1 - 4 * u) (3 * q + 2 - u) (q + 1 - u) ∪
    row (3 * q + 2 - 5 * u) (2 * q + 1 - 2 * u) (3 * u - q) ∪
    row (2 * q + 2 - 2 * u) (4 * q + 3 - 2 * u) (2 * u) ∪
    row (2 * q + 2) (q + u + 1) (q - u) ∪
    row (3 * q + 2 - u) (2 * q + 1) (q + 1 - u) ∪
    row (4 * q + 3 - 2 * u) 0 (2 * u)

/-- The family `R3Q` solves `SP(l, δ)` with `l = 4 * q + 3`, `δ = 2 * q + 2 - 2 * u` (`μ = 4 * q + 3 - 4 * u`) on its whole domain. -/
theorem famR3Q_sp (q u : ℤ)
    (h1 : q + 1 ≤ 3 * u) (h2 : 2 * u ≤ q) :
    SP (4 * q + 3) (2 * q + 2 - 2 * u) (famR3Q q u) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [famR3Q, image_union_fst, Finset.mem_union, mem_image_fst_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famR3Q, image_union_snd, Finset.mem_union, mem_image_snd_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famR3Q, image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc, or_assoc]
    constructor
    · intro h
      omega
    · intro hx
      rcases Int.emod_two_eq x with hp | hp
      · rcases le_or_gt x (-2 * q - 2 * u - 2) with c | c
        · pick_run
        rcases le_or_gt x (2 * u - 2 * q - 2) with c | c
        · pick_run
        rcases le_or_gt x 0 with c | c
        · pick_run
        rcases le_or_gt x (2 * q - 2 * u) with c | c
        · pick_run
        rcases le_or_gt x (4 * u) with c | c
        · pick_run
        rcases le_or_gt x (4 * q + 2 - 4 * u) with c | c
        · pick_run
        pick_run
      · rcases le_or_gt x (4 * u - 4 * q - 3) with c | c
        · pick_run
        rcases le_or_gt x (-4 * u - 1) with c | c
        · pick_run
        rcases le_or_gt x (2 * u - 2 * q - 1) with c | c
        · pick_run
        rcases le_or_gt x (-1) with c | c
        · pick_run
        rcases le_or_gt x (2 * q + 1 - 2 * u) with c | c
        · pick_run
        rcases le_or_gt x (2 * q + 2 * u + 1) with c | c
        · pick_run
        pick_run
  · unfold famR3Q
    exact (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le
      (card_union_le_of_le (card_union_le_of_le (card_row_le _ _ _) (card_row_le _ _ _))
      (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _))
      (card_row_le _ _ _)).trans (by omega)
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 2 * u, n = 2 * q + 1 - 4 * u; value [4 * u + 2, 4 * q + 2 - 4 * u]; mirror [4 * u - 4 * q - 1, -4 * u - 1]; P
--   b1: a = 2 * q + 1 - 4 * u, c = 3 * q + 2 - u, n = q + 1 - u; value [2 * q + 2 * u + 3, 4 * q + 3]; mirror [-4 * q - 2, -2 * q - 2 * u - 2]; P
--   b2: a = 3 * q + 2 - 5 * u, c = 2 * q + 1 - 2 * u, n = 3 * u - q; value [2 * q + 2 - 2 * u, 4 * u]; mirror [1 - 4 * u, 2 * u - 2 * q - 1]; P
--   b3: a = 2 * q + 2 - 2 * u, c = 4 * q + 3 - 2 * u, n = 2 * u; value [4 * q + 4 - 4 * u, 4 * q + 2]; mirror [-4 * q - 1, 4 * u - 4 * q - 3]; P
--   b4: a = 2 * q + 2, c = q + u + 1, n = q - u; value [2, 2 * q - 2 * u]; mirror [2 * u + 1 - 2 * q, -1]; P
--   b5: a = 3 * q + 2 - u, c = 2 * q + 1, n = q + 1 - u; value [1, 2 * q + 1 - 2 * u]; mirror [2 * u - 2 * q, 0]; P
--   b6: a = 4 * q + 3 - 2 * u, c = 0, n = 2 * u; value [-2 * q - 2 * u, 2 * u - 2 * q - 2]; mirror [2 * q + 3 - 2 * u, 2 * q + 2 * u + 1]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b5.value [1, 2 * q + 1 - 2 * u] | b6.mirror [2 * q + 3 - 2 * u, 2 * q + 2 * u + 1] | b1.value [2 * q + 2 * u + 3, 4 * q + 3]
--   x ≥ 1, x even: b4.value [2, 2 * q - 2 * u] | b2.value [2 * q + 2 - 2 * u, 4 * u] | b0.value [4 * u + 2, 4 * q + 2 - 4 * u] | b3.value [4 * q + 4 - 4 * u, 4 * q + 2]
--   x ≤ 0, x odd: b3.mirror [-4 * q - 1, 4 * u - 4 * q - 3] | b0.mirror [4 * u - 4 * q - 1, -4 * u - 1] | b2.mirror [1 - 4 * u, 2 * u - 2 * q - 1] | b4.mirror [2 * u + 1 - 2 * q, -1]
--   x ≤ 0, x even: b1.mirror [-4 * q - 2, -2 * q - 2 * u - 2] | b6.value [-2 * q - 2 * u, 2 * u - 2 * q - 2] | b5.mirror [2 * u - 2 * q, 0]

/-- The block-reversal family `R3T1` (l = 4q + 3, μ = l - 2, 6 blocks, target order `513042`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famR3T1 (q : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (q + 2) q ∪
    row q 1 q ∪
    row (2 * q) (3 * q + 2) (q + 1) ∪
    row (3 * q + 1) (q + 1) 1 ∪
    row (3 * q + 2) (2 * q + 2) q ∪
    row (4 * q + 2) 0 1

/-- The family `R3T1` solves `SP(l, δ)` with `l = 4 * q + 3`, `δ = 2 * q + 1` (`μ = 4 * q + 1`) on its whole domain. -/
theorem famR3T1_sp (q : ℤ)
    (h1 : 1 ≤ q) :
    SP (4 * q + 3) (2 * q + 1) (famR3T1 q) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [famR3T1, image_union_fst, Finset.mem_union, mem_image_fst_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famR3T1, image_union_snd, Finset.mem_union, mem_image_snd_row, Finset.mem_Icc]
    omega
  · ext x
    simp only [famR3T1, image_union_val, image_union_mir, Finset.mem_union, mem_image_val_row,
      mem_image_mir_row, Finset.mem_Icc, or_assoc]
    constructor
    · intro h
      omega
    · intro hx
      rcases Int.emod_two_eq x with hp | hp
      · rcases le_or_gt x (-2 * q - 2) with c | c
        · pick_run
        rcases le_or_gt x (-2) with c | c
        · pick_run
        rcases le_or_gt x 0 with c | c
        · pick_run
        rcases le_or_gt x (2 * q) with c | c
        · pick_run
        rcases le_or_gt x (2 * q + 2) with c | c
        · pick_run
        pick_run
      · rcases le_or_gt x (-2 * q - 3) with c | c
        · pick_run
        rcases le_or_gt x (-2 * q - 1) with c | c
        · pick_run
        rcases le_or_gt x (-1) with c | c
        · pick_run
        rcases le_or_gt x 1 with c | c
        · pick_run
        rcases le_or_gt x (2 * q + 1) with c | c
        · pick_run
        pick_run
  · unfold famR3T1
    exact (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le (card_union_le_of_le
      (card_union_le_of_le (card_row_le _ _ _) (card_row_le _ _ _)) (card_row_le _ _ _))
      (card_row_le _ _ _)) (card_row_le _ _ _)) (card_row_le _ _ _)).trans (by omega)
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = q + 2, n = q; value [2 * q + 4, 4 * q + 2]; mirror [-4 * q - 1, -2 * q - 3]; P
--   b1: a = q, c = 1, n = q; value [3, 2 * q + 1]; mirror [-2 * q, -2]; P
--   b2: a = 2 * q, c = 3 * q + 2, n = q + 1; value [2 * q + 3, 4 * q + 3]; mirror [-4 * q - 2, -2 * q - 2]; P
--   b3: a = 3 * q + 1, c = q + 1, n = 1; value [1, 1]; mirror [0, 0]; P
--   b4: a = 3 * q + 2, c = 2 * q + 2, n = q; value [2, 2 * q]; mirror [1 - 2 * q, -1]; P
--   b5: a = 4 * q + 2, c = 0, n = 1; value [-2 * q - 1, -2 * q - 1]; mirror [2 * q + 2, 2 * q + 2]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b3.value [1, 1] | b1.value [3, 2 * q + 1] | b2.value [2 * q + 3, 4 * q + 3]
--   x ≥ 1, x even: b4.value [2, 2 * q] | b5.mirror [2 * q + 2, 2 * q + 2] | b0.value [2 * q + 4, 4 * q + 2]
--   x ≤ 0, x odd: b0.mirror [-4 * q - 1, -2 * q - 3] | b5.value [-2 * q - 1, -2 * q - 1] | b4.mirror [1 - 2 * q, -1]
--   x ≤ 0, x even: b2.mirror [-4 * q - 2, -2 * q - 2] | b1.mirror [-2 * q, -2] | b3.mirror [0, 0]

end L2
