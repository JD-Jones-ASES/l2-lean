import L2.SP

/-!
# Block-reversal families for `l ≡ 1 (mod 4)`

The families `FA1`, `FA3`, `FT`, `FL1`, `FL5`. Each is a union of rows (block reversals)
whose sizes are affine in the parameters, and each solves `SP(l, δ)` on its whole domain: the
value runs and mirror runs of its rows tile `[1 − l, l]`.
-/

namespace L2

/-- The block-reversal family `FA1` (l = 4q + 1, μ = 4s + 1, 8 blocks, target order `71340526`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famFA1 (q s : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (4 * q - 3 * s) s ∪
    row s (2 * q - 2 * s) (s - 1) ∪
    row (2 * s - 1) (3 * q) q ∪
    row (q + 2 * s - 1) (2 * q - s - 1) (q - s) ∪
    row (2 * q + s - 1) (3 * q - 2 * s - 1) (q + 1 - s) ∪
    row (3 * q) (4 * q - 2 * s) (2 * s - q) ∪
    row (2 * q + 2 * s) (4 * q) 1 ∪
    row (2 * q + 2 * s + 1) 0 (2 * q - 2 * s)

/-- The family `FA1` solves `SP(l, δ)` with `l = 4 * q + 1`, `δ = 2 * s + 1` (`μ = 4 * s + 1`) on its whole domain. -/
theorem famFA1_sp (q s : ℤ)
    (h1 : q + 1 ≤ 2 * s) (h2 : s + 1 ≤ q) :
    SP (4 * q + 1) (2 * s + 1) (famFA1 q s) := by
  sorry
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 4 * q - 3 * s, n = s; value [4 * q + 2 - 2 * s, 4 * q]; mirror [1 - 4 * q, 2 * s - 4 * q - 1]; P
--   b1: a = s, c = 2 * q - 2 * s, n = s - 1; value [2 * q + 3 - 2 * s, 2 * q - 1]; mirror [2 - 2 * q, 2 * s - 2 * q - 2]; P
--   b2: a = 2 * s - 1, c = 3 * q, n = q; value [2 * q + 3, 4 * q + 1]; mirror [-4 * q, -2 * q - 2]; P
--   b3: a = q + 2 * s - 1, c = 2 * q - s - 1, n = q - s; value [2, 2 * q - 2 * s]; mirror [2 * s + 1 - 2 * q, -1]; P
--   b4: a = 2 * q + s - 1, c = 3 * q - 2 * s - 1, n = q + 1 - s; value [1, 2 * q + 1 - 2 * s]; mirror [2 * s - 2 * q, 0]; P
--   b5: a = 3 * q, c = 4 * q - 2 * s, n = 2 * s - q; value [2 * q + 2 - 2 * s, 2 * s]; mirror [1 - 2 * s, 2 * s - 2 * q - 1]; P
--   b6: a = 2 * q + 2 * s, c = 4 * q, n = 1; value [2 * q + 1, 2 * q + 1]; mirror [-2 * q, -2 * q]; P
--   b7: a = 2 * q + 2 * s + 1, c = 0, n = 2 * q - 2 * s; value [2 * s + 1 - 4 * q, -2 * s - 1]; mirror [2 * s + 2, 4 * q - 2 * s]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b4.value [1, 2 * q + 1 - 2 * s] | b1.value [2 * q + 3 - 2 * s, 2 * q - 1] | b6.value [2 * q + 1, 2 * q + 1] | b2.value [2 * q + 3, 4 * q + 1]
--   x ≥ 1, x even: b3.value [2, 2 * q - 2 * s] | b5.value [2 * q + 2 - 2 * s, 2 * s] | b7.mirror [2 * s + 2, 4 * q - 2 * s] | b0.value [4 * q + 2 - 2 * s, 4 * q]
--   x ≤ 0, x odd: b0.mirror [1 - 4 * q, 2 * s - 4 * q - 1] | b7.value [2 * s + 1 - 4 * q, -2 * s - 1] | b5.mirror [1 - 2 * s, 2 * s - 2 * q - 1] | b3.mirror [2 * s + 1 - 2 * q, -1]
--   x ≤ 0, x even: b2.mirror [-4 * q, -2 * q - 2] | b6.mirror [-2 * q, -2 * q] | b1.mirror [2 - 2 * q, 2 * s - 2 * q - 2] | b4.mirror [2 * s - 2 * q, 0]

/-- The block-reversal family `FA3` (l = 4q + 1, μ = 4s + 3, 7 blocks, target order `6134052`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famFA3 (q s : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (4 * q - 3 * s - 1) (s + 1) ∪
    row (s + 1) (2 * q - 2 * s - 1) (s + 1) ∪
    row (2 * s + 2) (3 * q + 1) q ∪
    row (q + 2 * s + 2) (2 * q - s) (q - s - 1) ∪
    row (2 * q + s + 1) (3 * q - 2 * s - 1) (q - s) ∪
    row (3 * q + 1) (4 * q - 2 * s) (2 * s + 1 - q) ∪
    row (2 * q + 2 * s + 2) 0 (2 * q - 2 * s - 1)

/-- The family `FA3` solves `SP(l, δ)` with `l = 4 * q + 1`, `δ = 2 * s + 2` (`μ = 4 * s + 3`) on its whole domain. -/
theorem famFA3_sp (q s : ℤ)
    (h1 : q ≤ 2 * s) (h2 : s + 2 ≤ q) :
    SP (4 * q + 1) (2 * s + 2) (famFA3 q s) := by
  sorry
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 4 * q - 3 * s - 1, n = s + 1; value [4 * q + 1 - 2 * s, 4 * q + 1]; mirror [-4 * q, 2 * s - 4 * q]; P
--   b1: a = s + 1, c = 2 * q - 2 * s - 1, n = s + 1; value [2 * q - 2 * s, 2 * q]; mirror [1 - 2 * q, 2 * s + 1 - 2 * q]; P
--   b2: a = 2 * s + 2, c = 3 * q + 1, n = q; value [2 * q + 2, 4 * q]; mirror [1 - 4 * q, -2 * q - 1]; P
--   b3: a = q + 2 * s + 2, c = 2 * q - s, n = q - s - 1; value [2, 2 * q - 2 * s - 2]; mirror [2 * s + 3 - 2 * q, -1]; P
--   b4: a = 2 * q + s + 1, c = 3 * q - 2 * s - 1, n = q - s; value [1, 2 * q - 2 * s - 1]; mirror [2 * s + 2 - 2 * q, 0]; P
--   b5: a = 3 * q + 1, c = 4 * q - 2 * s, n = 2 * s + 1 - q; value [2 * q + 1 - 2 * s, 2 * s + 1]; mirror [-2 * s, 2 * s - 2 * q]; P
--   b6: a = 2 * q + 2 * s + 2, c = 0, n = 2 * q - 2 * s - 1; value [2 * s + 2 - 4 * q, -2 * s - 2]; mirror [2 * s + 3, 4 * q - 2 * s - 1]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b4.value [1, 2 * q - 2 * s - 1] | b5.value [2 * q + 1 - 2 * s, 2 * s + 1] | b6.mirror [2 * s + 3, 4 * q - 2 * s - 1] | b0.value [4 * q + 1 - 2 * s, 4 * q + 1]
--   x ≥ 1, x even: b3.value [2, 2 * q - 2 * s - 2] | b1.value [2 * q - 2 * s, 2 * q] | b2.value [2 * q + 2, 4 * q]
--   x ≤ 0, x odd: b2.mirror [1 - 4 * q, -2 * q - 1] | b1.mirror [1 - 2 * q, 2 * s + 1 - 2 * q] | b3.mirror [2 * s + 3 - 2 * q, -1]
--   x ≤ 0, x even: b0.mirror [-4 * q, 2 * s - 4 * q] | b6.value [2 * s + 2 - 4 * q, -2 * s - 2] | b5.mirror [-2 * s, 2 * s - 2 * q] | b4.mirror [2 * s + 2 - 2 * q, 0]

/-- The block-reversal family `FT` (l = 4q + 1, μ = l - 2, 6 blocks, target order `513042`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famFT (q : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (q + 1) q ∪
    row q 1 (q - 1) ∪
    row (2 * q - 1) (3 * q + 1) q ∪
    row (3 * q - 1) q 1 ∪
    row (3 * q) (2 * q + 1) q ∪
    row (4 * q) 0 1

/-- The family `FT` solves `SP(l, δ)` with `l = 4 * q + 1`, `δ = 2 * q` (`μ = 4 * q - 1`) on its whole domain. -/
theorem famFT_sp (q : ℤ)
    (h1 : 2 ≤ q) :
    SP (4 * q + 1) (2 * q) (famFT q) := by
  sorry
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = q + 1, n = q; value [2 * q + 2, 4 * q]; mirror [1 - 4 * q, -2 * q - 1]; P
--   b1: a = q, c = 1, n = q - 1; value [3, 2 * q - 1]; mirror [2 - 2 * q, -2]; P
--   b2: a = 2 * q - 1, c = 3 * q + 1, n = q; value [2 * q + 3, 4 * q + 1]; mirror [-4 * q, -2 * q - 2]; P
--   b3: a = 3 * q - 1, c = q, n = 1; value [1, 1]; mirror [0, 0]; P
--   b4: a = 3 * q, c = 2 * q + 1, n = q; value [2, 2 * q]; mirror [1 - 2 * q, -1]; P
--   b5: a = 4 * q, c = 0, n = 1; value [-2 * q, -2 * q]; mirror [2 * q + 1, 2 * q + 1]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b3.value [1, 1] | b1.value [3, 2 * q - 1] | b5.mirror [2 * q + 1, 2 * q + 1] | b2.value [2 * q + 3, 4 * q + 1]
--   x ≥ 1, x even: b4.value [2, 2 * q] | b0.value [2 * q + 2, 4 * q]
--   x ≤ 0, x odd: b0.mirror [1 - 4 * q, -2 * q - 1] | b4.mirror [1 - 2 * q, -1]
--   x ≤ 0, x even: b2.mirror [-4 * q, -2 * q - 2] | b5.value [-2 * q, -2 * q] | b1.mirror [2 - 2 * q, -2] | b3.mirror [0, 0]

/-- The block-reversal family `FL1` (l = 8p + 1, μ = 4p + 1, 7 blocks, target order `6024513`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famFL1 (p : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (2 * p) 1 ∪
    row 1 (5 * p + 1) p ∪
    row (p + 1) (2 * p + 1) (p - 1) ∪
    row (2 * p) (6 * p + 1) (2 * p) ∪
    row (4 * p) (3 * p) p ∪
    row (5 * p) (4 * p) (p + 1) ∪
    row (6 * p + 1) 0 (2 * p)

/-- The family `FL1` solves `SP(l, δ)` with `l = 8 * p + 1`, `δ = 2 * p + 1` (`μ = 4 * p + 1`) on its whole domain. -/
theorem famFL1_sp (p : ℤ)
    (h1 : 2 ≤ p) :
    SP (8 * p + 1) (2 * p + 1) (famFL1 p) := by
  sorry
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 2 * p, n = 1; value [4 * p + 1, 4 * p + 1]; mirror [-4 * p, -4 * p]; P
--   b1: a = 1, c = 5 * p + 1, n = p; value [6 * p + 2, 8 * p]; mirror [1 - 8 * p, -6 * p - 1]; P
--   b2: a = p + 1, c = 2 * p + 1, n = p - 1; value [2 * p + 3, 4 * p - 1]; mirror [2 - 4 * p, -2 * p - 2]; P
--   b3: a = 2 * p, c = 6 * p + 1, n = 2 * p; value [4 * p + 3, 8 * p + 1]; mirror [-8 * p, -4 * p - 2]; P
--   b4: a = 4 * p, c = 3 * p, n = p; value [2, 2 * p]; mirror [1 - 2 * p, -1]; P
--   b5: a = 5 * p, c = 4 * p, n = p + 1; value [1, 2 * p + 1]; mirror [-2 * p, 0]; P
--   b6: a = 6 * p + 1, c = 0, n = 2 * p; value [1 - 6 * p, -2 * p - 1]; mirror [2 * p + 2, 6 * p]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b5.value [1, 2 * p + 1] | b2.value [2 * p + 3, 4 * p - 1] | b0.value [4 * p + 1, 4 * p + 1] | b3.value [4 * p + 3, 8 * p + 1]
--   x ≥ 1, x even: b4.value [2, 2 * p] | b6.mirror [2 * p + 2, 6 * p] | b1.value [6 * p + 2, 8 * p]
--   x ≤ 0, x odd: b1.mirror [1 - 8 * p, -6 * p - 1] | b6.value [1 - 6 * p, -2 * p - 1] | b4.mirror [1 - 2 * p, -1]
--   x ≤ 0, x even: b3.mirror [-8 * p, -4 * p - 2] | b0.mirror [-4 * p, -4 * p] | b2.mirror [2 - 4 * p, -2 * p - 2] | b5.mirror [-2 * p, 0]

/-- The block-reversal family `FL5` (l = 8p + 5, μ = 4p + 3, 6 blocks, target order `513402`): block `i` sends the sources
`[aᵢ + 1, aᵢ + nᵢ]` onto the targets `[cᵢ + 1, cᵢ + nᵢ]` reversed. -/
def famFL5 (p : ℤ) : Finset (ℤ × ℤ) :=
  row 0 (5 * p + 3) (p + 1) ∪
    row (p + 1) (2 * p + 1) (p + 1) ∪
    row (2 * p + 2) (6 * p + 4) (2 * p + 1) ∪
    row (4 * p + 3) (3 * p + 2) p ∪
    row (5 * p + 3) (4 * p + 2) (p + 1) ∪
    row (6 * p + 4) 0 (2 * p + 1)

/-- The family `FL5` solves `SP(l, δ)` with `l = 8 * p + 5`, `δ = 2 * p + 2` (`μ = 4 * p + 3`) on its whole domain. -/
theorem famFL5_sp (p : ℤ)
    (h1 : 1 ≤ p) :
    SP (8 * p + 5) (2 * p + 2) (famFL5 p) := by
  sorry
-- Blocks (source order): a, c, n; value run [lo, hi] (step 2 down from hi); mirror run [lo, hi]; type
--   b0: a = 0, c = 5 * p + 3, n = p + 1; value [6 * p + 5, 8 * p + 5]; mirror [-8 * p - 4, -6 * p - 4]; P
--   b1: a = p + 1, c = 2 * p + 1, n = p + 1; value [2 * p + 2, 4 * p + 2]; mirror [-4 * p - 1, -2 * p - 1]; P
--   b2: a = 2 * p + 2, c = 6 * p + 4, n = 2 * p + 1; value [4 * p + 4, 8 * p + 4]; mirror [-8 * p - 3, -4 * p - 3]; P
--   b3: a = 4 * p + 3, c = 3 * p + 2, n = p; value [2, 2 * p]; mirror [1 - 2 * p, -1]; P
--   b4: a = 5 * p + 3, c = 4 * p + 2, n = p + 1; value [1, 2 * p + 1]; mirror [-2 * p, 0]; P
--   b5: a = 6 * p + 4, c = 0, n = 2 * p + 1; value [-6 * p - 2, -2 * p - 2]; mirror [2 * p + 3, 6 * p + 3]; N
-- Chains (the x in each case lies in exactly one piece; pieces abut with step 2):
--   x ≥ 1, x odd: b4.value [1, 2 * p + 1] | b5.mirror [2 * p + 3, 6 * p + 3] | b0.value [6 * p + 5, 8 * p + 5]
--   x ≥ 1, x even: b3.value [2, 2 * p] | b1.value [2 * p + 2, 4 * p + 2] | b2.value [4 * p + 4, 8 * p + 4]
--   x ≤ 0, x odd: b2.mirror [-8 * p - 3, -4 * p - 3] | b1.mirror [-4 * p - 1, -2 * p - 1] | b3.mirror [1 - 2 * p, -1]
--   x ≤ 0, x even: b0.mirror [-8 * p - 4, -6 * p - 4] | b5.value [-6 * p - 2, -2 * p - 2] | b4.mirror [-2 * p, 0]

end L2
