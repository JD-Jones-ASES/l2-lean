import L2.SP

/-!
# Block-reversal families for `l ≡ 0 (mod 4)`, first part

The families `A1`, `A3`, `U1`, `U3` of order `l = 4q`. Each is a union of rows (block
reversals) whose sizes are affine in the parameters, and each solves `SP(l, δ)` on its whole
domain: the value runs and mirror runs of its rows tile `[1 − l, l]`.
-/

namespace L2

/-- The block-reversal family `A1` (l = 4q, μ = 4s + 1, 9 blocks, target order `836720514`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famA1 (q s : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (4 * q - 3 * s - 1) s ∪
    row s (4 * q - s - 1) 1 ∪
    row (s + 1) (3 * q - 2 * s - 1) (q - s) ∪
    row (q + 1) 1 (2 * s + 1 - q) ∪
    row (2 * s + 2) (4 * q - s) s ∪
    row (3 * s + 2) (4 * q - 2 * s - 1) s ∪
    row (4 * s + 2) (2 * s + 2 - q) (3 * q - 4 * s - 2) ∪
    row (3 * q) (2 * q - 2 * s) (q - 1) ∪
    row (4 * q - 1) 0 1

/-- The family `A1` solves `SP(l, δ)` with `l = 4 * q`, `δ = 2 * s + 1` (`μ = 4 * s + 1`) on its whole domain. -/
theorem famA1_sp (q s : ℤ)
    (h1 : q ≤ 2 * s) (h2 : q ≤ 2 * s + 1) (h3 : 1 ≤ s) (h4 : s + 1 ≤ q) (h5 : s + 1 ≤ q) (h6 : 2 ≤ q)
    (h7 : 1 ≤ q) (h8 : 1 ≤ q) (h9 : s + 1 ≤ 2 * q) (h10 : s + 1 ≤ 2 * q) (h11 : s ≤ 2 * q)
    (h12 : 4 * s + 3 ≤ 3 * q) :
    SP (4 * q) (2 * s + 1) (famA1 q s) := by
  sorry
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 4 * q - 3 * s - 1, n = s; value [4 * q + 1 - 2 * s, 4 * q - 1]; mirror [2 - 4 * q, 2 * s - 4 * q]; P
--   b1: a = s, c = 4 * q - s - 1, n = 1; value [4 * q, 4 * q]; mirror [1 - 4 * q, 1 - 4 * q]; P
--   b2: a = s + 1, c = 3 * q - 2 * s - 1, n = q - s; value [2 * q, 4 * q - 2 * s - 2]; mirror [2 * s + 3 - 4 * q, 1 - 2 * q]; P
--   b3: a = q + 1, c = 1, n = 2 * s + 1 - q; value [1, 4 * s + 1 - 2 * q]; mirror [2 * q - 4 * s, 0]; P
--   b4: a = 2 * s + 2, c = 4 * q - s, n = s; value [4 * q - 2 * s, 4 * q - 2]; mirror [3 - 4 * q, 2 * s + 1 - 4 * q]; P
--   b5: a = 3 * s + 2, c = 4 * q - 2 * s - 1, n = s; value [4 * q - 4 * s - 1, 4 * q - 2 * s - 3]; mirror [2 * s + 4 - 4 * q, 4 * s + 2 - 4 * q]; P
--   b6: a = 4 * s + 2, c = 2 * s + 2 - q, n = 3 * q - 4 * s - 2; value [4 * s + 4 - 4 * q, 2 * q - 4 * s - 2]; mirror [4 * s + 3 - 2 * q, 4 * q - 4 * s - 3]; N
--   b7: a = 3 * q, c = 2 * q - 2 * s, n = q - 1; value [3 - 2 * q, -1]; mirror [2, 2 * q - 2]; N
--   b8: a = 4 * q - 1, c = 0, n = 1; value [2 * s + 2 - 4 * q, 2 * s + 2 - 4 * q]; mirror [4 * q - 2 * s - 1, 4 * q - 2 * s - 1]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b3.value [1, 4 * s + 1 - 2 * q] | b6.mirror [4 * s + 3 - 2 * q, 4 * q - 4 * s - 3] | b5.value [4 * q - 4 * s - 1, 4 * q - 2 * s - 3] | b8.mirror [4 * q - 2 * s - 1, 4 * q - 2 * s - 1] | b0.value [4 * q + 1 - 2 * s, 4 * q - 1]
--   x ≥ 1, x even: b7.mirror [2, 2 * q - 2] | b2.value [2 * q, 4 * q - 2 * s - 2] | b4.value [4 * q - 2 * s, 4 * q - 2] | b1.value [4 * q, 4 * q]
--   x ≤ 0, x odd: b1.mirror [1 - 4 * q, 1 - 4 * q] | b4.mirror [3 - 4 * q, 2 * s + 1 - 4 * q] | b2.mirror [2 * s + 3 - 4 * q, 1 - 2 * q] | b7.value [3 - 2 * q, -1]
--   x ≤ 0, x even: b0.mirror [2 - 4 * q, 2 * s - 4 * q] | b8.value [2 * s + 2 - 4 * q, 2 * s + 2 - 4 * q] | b5.mirror [2 * s + 4 - 4 * q, 4 * s + 2 - 4 * q] | b6.value [4 * s + 4 - 4 * q, 2 * q - 4 * s - 2] | b3.mirror [2 * q - 4 * s, 0]

/-- The block-reversal family `A3` (l = 4q, μ = 4s + 3, 9 blocks, target order `836720514`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famA3 (q s : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (4 * q - 3 * s - 3) (s + 1) ∪
    row (s + 1) (4 * q - s - 1) 1 ∪
    row (s + 2) (3 * q - 2 * s - 2) (q - s - 1) ∪
    row (q + 1) 1 (2 * s + 2 - q) ∪
    row (2 * s + 3) (4 * q - s) s ∪
    row (3 * s + 3) (4 * q - 2 * s - 2) (s + 1) ∪
    row (4 * s + 4) (2 * s + 3 - q) (3 * q - 4 * s - 4) ∪
    row (3 * q) (2 * q - 2 * s - 1) (q - 1) ∪
    row (4 * q - 1) 0 1

/-- The family `A3` solves `SP(l, δ)` with `l = 4 * q`, `δ = 2 * s + 2` (`μ = 4 * s + 3`) on its whole domain. -/
theorem famA3_sp (q s : ℤ)
    (h1 : q ≤ 2 * s + 1) (h2 : q ≤ 2 * s + 2) (h3 : 1 ≤ s) (h4 : 0 ≤ s) (h5 : s + 2 ≤ q) (h6 : s + 1 ≤ q)
    (h7 : 2 ≤ q) (h8 : 1 ≤ q) (h9 : 1 ≤ q) (h10 : s + 2 ≤ 2 * q) (h11 : s + 1 ≤ 2 * q) (h12 : s + 1 ≤ 2 * q)
    (h13 : 4 * s + 5 ≤ 3 * q) :
    SP (4 * q) (2 * s + 2) (famA3 q s) := by
  sorry
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 4 * q - 3 * s - 3, n = s + 1; value [4 * q - 2 * s - 1, 4 * q - 1]; mirror [2 - 4 * q, 2 * s + 2 - 4 * q]; P
--   b1: a = s + 1, c = 4 * q - s - 1, n = 1; value [4 * q, 4 * q]; mirror [1 - 4 * q, 1 - 4 * q]; P
--   b2: a = s + 2, c = 3 * q - 2 * s - 2, n = q - s - 1; value [2 * q, 4 * q - 2 * s - 4]; mirror [2 * s + 5 - 4 * q, 1 - 2 * q]; P
--   b3: a = q + 1, c = 1, n = 2 * s + 2 - q; value [1, 4 * s + 3 - 2 * q]; mirror [2 * q - 4 * s - 2, 0]; P
--   b4: a = 2 * s + 3, c = 4 * q - s, n = s; value [4 * q - 2 * s, 4 * q - 2]; mirror [3 - 4 * q, 2 * s + 1 - 4 * q]; P
--   b5: a = 3 * s + 3, c = 4 * q - 2 * s - 2, n = s + 1; value [4 * q - 4 * s - 3, 4 * q - 2 * s - 3]; mirror [2 * s + 4 - 4 * q, 4 * s + 4 - 4 * q]; P
--   b6: a = 4 * s + 4, c = 2 * s + 3 - q, n = 3 * q - 4 * s - 4; value [4 * s + 6 - 4 * q, 2 * q - 4 * s - 4]; mirror [4 * s + 5 - 2 * q, 4 * q - 4 * s - 5]; N
--   b7: a = 3 * q, c = 2 * q - 2 * s - 1, n = q - 1; value [3 - 2 * q, -1]; mirror [2, 2 * q - 2]; N
--   b8: a = 4 * q - 1, c = 0, n = 1; value [2 * s + 3 - 4 * q, 2 * s + 3 - 4 * q]; mirror [4 * q - 2 * s - 2, 4 * q - 2 * s - 2]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b3.value [1, 4 * s + 3 - 2 * q] | b6.mirror [4 * s + 5 - 2 * q, 4 * q - 4 * s - 5] | b5.value [4 * q - 4 * s - 3, 4 * q - 2 * s - 3] | b0.value [4 * q - 2 * s - 1, 4 * q - 1]
--   x ≥ 1, x even: b7.mirror [2, 2 * q - 2] | b2.value [2 * q, 4 * q - 2 * s - 4] | b8.mirror [4 * q - 2 * s - 2, 4 * q - 2 * s - 2] | b4.value [4 * q - 2 * s, 4 * q - 2] | b1.value [4 * q, 4 * q]
--   x ≤ 0, x odd: b1.mirror [1 - 4 * q, 1 - 4 * q] | b4.mirror [3 - 4 * q, 2 * s + 1 - 4 * q] | b8.value [2 * s + 3 - 4 * q, 2 * s + 3 - 4 * q] | b2.mirror [2 * s + 5 - 4 * q, 1 - 2 * q] | b7.value [3 - 2 * q, -1]
--   x ≤ 0, x even: b0.mirror [2 - 4 * q, 2 * s + 2 - 4 * q] | b5.mirror [2 * s + 4 - 4 * q, 4 * s + 4 - 4 * q] | b6.value [4 * s + 6 - 4 * q, 2 * q - 4 * s - 4] | b3.mirror [2 * q - 4 * s - 2, 0]

/-- The block-reversal family `U1` (l = 4q, μ = 8s + 1, 8 blocks, target order `57134026`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famU1 (q s : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (3 * q - 3 * s - 1) (q - s) ∪
    row (q - s) (2 * q - 4 * s) (3 * s - q) ∪
    row (2 * s) (4 * q - 4 * s - 1) (2 * s + 1) ∪
    row (4 * s + 1) (q - s) (q - s) ∪
    row (q + 3 * s + 1) (2 * q - 2 * s) (q - s - 1) ∪
    row (2 * q + 2 * s) 0 1 ∪
    row (2 * q + 2 * s + 1) (4 * q - 2 * s) (2 * s) ∪
    row (2 * q + 4 * s + 1) 1 (2 * q - 4 * s - 1)

/-- The family `U1` solves `SP(l, δ)` with `l = 4 * q`, `δ = 4 * s + 1` (`μ = 8 * s + 1`) on its whole domain. -/
theorem famU1_sp (q s : ℤ)
    (h1 : q + 1 ≤ 3 * s) (h2 : 1 ≤ s) (h3 : 0 ≤ s) (h4 : 0 ≤ s) (h5 : 2 * s + 1 ≤ q) (h6 : s + 2 ≤ q)
    (h7 : s + 1 ≤ q) (h8 : s + 1 ≤ q) (h9 : s + 1 ≤ q) (h10 : s ≤ q) (h11 : s ≤ q) (h12 : 0 ≤ q + s) :
    SP (4 * q) (4 * s + 1) (famU1 q s) := by
  sorry
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 3 * q - 3 * s - 1, n = q - s; value [2 * q + 2 * s + 1, 4 * q - 1]; mirror [2 - 4 * q, -2 * q - 2 * s]; P
--   b1: a = q - s, c = 2 * q - 4 * s, n = 3 * s - q; value [2 * q + 2 - 2 * s, 4 * s]; mirror [1 - 4 * s, 2 * s - 2 * q - 1]; P
--   b2: a = 2 * s, c = 4 * q - 4 * s - 1, n = 2 * s + 1; value [4 * q - 4 * s, 4 * q]; mirror [1 - 4 * q, 4 * s + 1 - 4 * q]; P
--   b3: a = 4 * s + 1, c = q - s, n = q - s; value [1, 2 * q - 2 * s - 1]; mirror [2 * s + 2 - 2 * q, 0]; P
--   b4: a = q + 3 * s + 1, c = 2 * q - 2 * s, n = q - s - 1; value [2, 2 * q - 2 * s - 2]; mirror [2 * s + 3 - 2 * q, -1]; P
--   b5: a = 2 * q + 2 * s, c = 0, n = 1; value [2 * s + 1 - 2 * q, 2 * s + 1 - 2 * q]; mirror [2 * q - 2 * s, 2 * q - 2 * s]; N
--   b6: a = 2 * q + 2 * s + 1, c = 4 * q - 2 * s, n = 2 * s; value [2 * q + 1 - 2 * s, 2 * q + 2 * s - 1]; mirror [2 - 2 * q - 2 * s, 2 * s - 2 * q]; P
--   b7: a = 2 * q + 4 * s + 1, c = 1, n = 2 * q - 4 * s - 1; value [4 * s + 3 - 4 * q, -4 * s - 1]; mirror [4 * s + 2, 4 * q - 4 * s - 2]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b3.value [1, 2 * q - 2 * s - 1] | b6.value [2 * q + 1 - 2 * s, 2 * q + 2 * s - 1] | b0.value [2 * q + 2 * s + 1, 4 * q - 1]
--   x ≥ 1, x even: b4.value [2, 2 * q - 2 * s - 2] | b5.mirror [2 * q - 2 * s, 2 * q - 2 * s] | b1.value [2 * q + 2 - 2 * s, 4 * s] | b7.mirror [4 * s + 2, 4 * q - 4 * s - 2] | b2.value [4 * q - 4 * s, 4 * q]
--   x ≤ 0, x odd: b2.mirror [1 - 4 * q, 4 * s + 1 - 4 * q] | b7.value [4 * s + 3 - 4 * q, -4 * s - 1] | b1.mirror [1 - 4 * s, 2 * s - 2 * q - 1] | b5.value [2 * s + 1 - 2 * q, 2 * s + 1 - 2 * q] | b4.mirror [2 * s + 3 - 2 * q, -1]
--   x ≤ 0, x even: b0.mirror [2 - 4 * q, -2 * q - 2 * s] | b6.mirror [2 - 2 * q - 2 * s, 2 * s - 2 * q] | b3.mirror [2 * s + 2 - 2 * q, 0]

/-- The block-reversal family `U3` (l = 4q, μ = 8s + 3, 9 blocks, target order `580364172`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famU3 (q s : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (2 * q - 4 * s - 1) (2 * s) ∪
    row (2 * s) (4 * q - 4 * s - 3) (2 * s + 1) ∪
    row (4 * s + 1) (3 * q + s) (q - s) ∪
    row (q + 3 * s + 1) (2 * q - 2 * s - 1) (q - s - 3) ∪
    row (2 * q + 2 * s - 2) (4 * q - 4 * s - 4) 1 ∪
    row (2 * q + 2 * s - 1) 0 1 ∪
    row (2 * q + 2 * s) (3 * q - 3 * s - 4) (q - s) ∪
    row (3 * q + s) (4 * q - 2 * s - 2) (3 * s + 2 - q) ∪
    row (2 * q + 4 * s + 2) 1 (2 * q - 4 * s - 2)

/-- The family `U3` solves `SP(l, δ)` with `l = 4 * q`, `δ = 4 * s + 2` (`μ = 8 * s + 3`) on its whole domain. -/
theorem famU3_sp (q s : ℤ)
    (h1 : q ≤ 3 * s + 1) (h2 : 1 ≤ s) (h3 : 0 ≤ s) (h4 : 0 ≤ s) (h5 : 2 * s + 2 ≤ q) (h6 : s + 4 ≤ q)
    (h7 : s + 2 ≤ q) (h8 : s + 2 ≤ q) (h9 : s + 1 ≤ q) (h10 : s + 1 ≤ q) (h11 : s ≤ q) (h12 : 0 ≤ q + s) :
    SP (4 * q) (4 * s + 2) (famU3 q s) := by
  sorry
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 2 * q - 4 * s - 1, n = 2 * s; value [2 * q + 2 - 2 * s, 2 * q + 2 * s]; mirror [1 - 2 * q - 2 * s, 2 * s - 2 * q - 1]; P
--   b1: a = 2 * s, c = 4 * q - 4 * s - 3, n = 2 * s + 1; value [4 * q - 4 * s - 1, 4 * q - 1]; mirror [2 - 4 * q, 4 * s + 2 - 4 * q]; P
--   b2: a = 4 * s + 1, c = 3 * q + s, n = q - s; value [2 * q + 2 * s + 2, 4 * q]; mirror [1 - 4 * q, -2 * q - 2 * s - 1]; P
--   b3: a = q + 3 * s + 1, c = 2 * q - 2 * s - 1, n = q - s - 3; value [4, 2 * q - 2 * s - 4]; mirror [2 * s + 5 - 2 * q, -3]; P
--   b4: a = 2 * q + 2 * s - 2, c = 4 * q - 4 * s - 4, n = 1; value [2 * q - 2 * s, 2 * q - 2 * s]; mirror [2 * s + 1 - 2 * q, 2 * s + 1 - 2 * q]; P
--   b5: a = 2 * q + 2 * s - 1, c = 0, n = 1; value [2 * s + 3 - 2 * q, 2 * s + 3 - 2 * q]; mirror [2 * q - 2 * s - 2, 2 * q - 2 * s - 2]; N
--   b6: a = 2 * q + 2 * s, c = 3 * q - 3 * s - 4, n = q - s; value [-1, 2 * q - 2 * s - 3]; mirror [2 * s + 4 - 2 * q, 2]; C
--   b7: a = 3 * q + s, c = 4 * q - 2 * s - 2, n = 3 * s + 2 - q; value [2 * q - 2 * s - 1, 4 * s + 1]; mirror [-4 * s, 2 * s + 2 - 2 * q]; P
--   b8: a = 2 * q + 4 * s + 2, c = 1, n = 2 * q - 4 * s - 2; value [4 * s + 4 - 4 * q, -4 * s - 2]; mirror [4 * s + 3, 4 * q - 4 * s - 3]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b6.value [1, 2 * q - 2 * s - 3] | b7.value [2 * q - 2 * s - 1, 4 * s + 1] | b8.mirror [4 * s + 3, 4 * q - 4 * s - 3] | b1.value [4 * q - 4 * s - 1, 4 * q - 1]
--   x ≥ 1, x even: b6.mirror [2, 2] | b3.value [4, 2 * q - 2 * s - 4] | b5.mirror [2 * q - 2 * s - 2, 2 * q - 2 * s - 2] | b4.value [2 * q - 2 * s, 2 * q - 2 * s] | b0.value [2 * q + 2 - 2 * s, 2 * q + 2 * s] | b2.value [2 * q + 2 * s + 2, 4 * q]
--   x ≤ 0, x odd: b2.mirror [1 - 4 * q, -2 * q - 2 * s - 1] | b0.mirror [1 - 2 * q - 2 * s, 2 * s - 2 * q - 1] | b4.mirror [2 * s + 1 - 2 * q, 2 * s + 1 - 2 * q] | b5.value [2 * s + 3 - 2 * q, 2 * s + 3 - 2 * q] | b3.mirror [2 * s + 5 - 2 * q, -3] | b6.value [-1, -1]
--   x ≤ 0, x even: b1.mirror [2 - 4 * q, 4 * s + 2 - 4 * q] | b8.value [4 * s + 4 - 4 * q, -4 * s - 2] | b7.mirror [-4 * s, 2 * s + 2 - 2 * q] | b6.mirror [2 * s + 4 - 2 * q, 0]

end L2
