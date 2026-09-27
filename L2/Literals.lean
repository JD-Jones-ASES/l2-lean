import L2.SP
import L2.Multi

/-!
# Literal certificates

Eleven solutions of the signed-permutation problem that serve as bases of the descent and as the
isolated cells of the band, and the sixteen two-fold Langford sequences of order at most four
(every cell `(d, l)` with `l ≤ 4` and `2d ≤ 3l + 1`), each split into two colours so that each colour
carries every difference once. Every one is checked by `decide`.
-/

namespace L2

/-- `σ = [6,4,7,3,5,2,1]` solves `SP(7, 2)` (`μ = 3`). -/
theorem sp_7_3 : SP 7 2 {(1, 6), (2, 4), (3, 7), (4, 3), (5, 5), (6, 2), (7, 1)} := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `σ = [3,5,2,4,1]` solves `SP(5, 2)` (`μ = 3`). -/
theorem sp_5_3 : SP 5 2 {(1, 3), (2, 5), (3, 2), (4, 4), (5, 1)} := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `σ = [6,5,9,8,1,7,4,3,2]` solves `SP(9, 3)` (`μ = 5`). -/
theorem sp_9_5 : SP 9 3 {(1, 6), (2, 5), (3, 9), (4, 8), (5, 1), (6, 7), (7, 4), (8, 3), (9, 2)} := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `σ = [2,6,8,7,5,4,3,1]` solves `SP(8, 3)` (`μ = 5`). -/
theorem sp_8_5 : SP 8 3 {(1, 2), (2, 6), (3, 8), (4, 7), (5, 5), (6, 4), (7, 3), (8, 1)} := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `σ = [1,5,4,8,7,2,6,3]` solves `SP(8, 4)` (`μ = 7`). -/
theorem sp_8_7 : SP 8 4 {(1, 1), (2, 5), (3, 4), (4, 8), (5, 7), (6, 2), (7, 6), (8, 3)} := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `σ = [7,6,5,1,12,11,10,4,9,8,3,2]` solves `SP(12, 5)` (`μ = 9`). -/
theorem sp_12_9 : SP 12 5 {(1, 7), (2, 6), (3, 5), (4, 1), (5, 12), (6, 11), (7, 10), (8, 4), (9, 9), (10, 8), (11, 3), (12, 2)} := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `σ = [2,1,3,9,8,12,11,10,7,6,5,4]` solves `SP(12, 6)` (`μ = 11`). -/
theorem sp_12_11 : SP 12 6 {(1, 2), (2, 1), (3, 3), (4, 9), (5, 8), (6, 12), (7, 11), (8, 10), (9, 7), (10, 6), (11, 5), (12, 4)} := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `σ = [1,4,12,11,10,16,15,14,13,9,8,7,6,5,3,2]` solves `SP(16, 6)` (`μ = 11`). -/
theorem sp_16_11 : SP 16 6 {(1, 1), (2, 4), (3, 12), (4, 11), (5, 10), (6, 16), (7, 15), (8, 14), (9, 13), (10, 9), (11, 8), (12, 7), (13, 6), (14, 5), (15, 3), (16, 2)} := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `σ = [2,1,14,13,12,11,10,20,19,18,17,16,15,7,6,5,4,3,9,8]` solves `SP(20, 8)` (`μ = 15`). -/
theorem sp_20_15 : SP 20 8 {(1, 2), (2, 1), (3, 14), (4, 13), (5, 12), (6, 11), (7, 10), (8, 20), (9, 19), (10, 18), (11, 17), (12, 16), (13, 15), (14, 7), (15, 6), (16, 5), (17, 4), (18, 3), (19, 9), (20, 8)} := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `σ = [2,1,17,16,15,14,13,12,24,23,22,21,20,19,18,9,8,7,6,5,4,3,11,10]` solves `SP(24, 9)` (`μ = 17`). -/
theorem sp_24_17 : SP 24 9 {(1, 2), (2, 1), (3, 17), (4, 16), (5, 15), (6, 14), (7, 13), (8, 12), (9, 24), (10, 23), (11, 22), (12, 21), (13, 20), (14, 19), (15, 18), (16, 9), (17, 8), (18, 7), (19, 6), (20, 5), (21, 4), (22, 3), (23, 11), (24, 10)} := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `σ = [2,1,23,22,21,20,19,18,17,16,15,3,32,31,30,29,28,27,26,25,24,11,10,9,8,7,6,5,4,14,13,12]` solves `SP(32, 12)` (`μ = 23`). -/
theorem sp_32_23 : SP 32 12 {(1, 2), (2, 1), (3, 23), (4, 22), (5, 21), (6, 20), (7, 19), (8, 18), (9, 17), (10, 16), (11, 15), (12, 3), (13, 32), (14, 31), (15, 30), (16, 29), (17, 28), (18, 27), (19, 26), (20, 25), (21, 24), (22, 11), (23, 10), (24, 9), (25, 8), (26, 7), (27, 6), (28, 5), (29, 4), (30, 14), (31, 13), (32, 12)} := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- A two-colour certificate for a two-fold Langford sequence of order 1 and defect 1. -/
theorem twoFold_lit_1_1 : TwoFold 1 1 {(1, 2)} {(3, 4)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 1 and defect 2. -/
theorem twoFold_lit_2_1 : TwoFold 2 1 {(1, 3)} {(2, 4)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 2 and defect 1. -/
theorem twoFold_lit_1_2 : TwoFold 1 2 {(1, 2), (3, 5)} {(4, 6), (7, 8)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 2 and defect 2. -/
theorem twoFold_lit_2_2 : TwoFold 2 2 {(1, 3), (2, 5)} {(4, 7), (6, 8)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 2 and defect 3. -/
theorem twoFold_lit_3_2 : TwoFold 3 2 {(1, 4), (2, 6)} {(3, 7), (5, 8)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 3 and defect 1. -/
theorem twoFold_lit_1_3 : TwoFold 1 3 {(1, 2), (5, 7), (6, 9)} {(3, 4), (8, 11), (10, 12)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 3 and defect 2. -/
theorem twoFold_lit_2_3 : TwoFold 2 3 {(1, 4), (2, 6), (9, 11)} {(3, 7), (5, 8), (10, 12)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 3 and defect 3. -/
theorem twoFold_lit_3_3 : TwoFold 3 3 {(1, 4), (2, 6), (3, 8)} {(5, 10), (7, 11), (9, 12)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 3 and defect 4. -/
theorem twoFold_lit_4_3 : TwoFold 4 3 {(1, 5), (2, 7), (3, 9)} {(4, 10), (6, 11), (8, 12)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 3 and defect 5. -/
theorem twoFold_lit_5_3 : TwoFold 5 3 {(1, 8), (2, 7), (3, 9)} {(4, 10), (5, 12), (6, 11)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 4 and defect 1. -/
theorem twoFold_lit_1_4 : TwoFold 1 4 {(1, 4), (2, 3), (5, 7), (6, 10)} {(8, 11), (9, 13), (12, 14), (15, 16)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 4 and defect 2. -/
theorem twoFold_lit_2_4 : TwoFold 2 4 {(1, 3), (2, 7), (4, 8), (10, 13)} {(5, 9), (6, 11), (12, 15), (14, 16)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 4 and defect 3. -/
theorem twoFold_lit_3_4 : TwoFold 3 4 {(1, 5), (3, 8), (7, 13), (11, 14)} {(2, 6), (4, 9), (10, 16), (12, 15)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 4 and defect 4. -/
theorem twoFold_lit_4_4 : TwoFold 4 4 {(1, 5), (2, 7), (3, 9), (4, 11)} {(6, 13), (8, 14), (10, 15), (12, 16)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 4 and defect 5. -/
theorem twoFold_lit_5_4 : TwoFold 5 4 {(1, 6), (2, 8), (3, 10), (4, 12)} {(5, 13), (7, 14), (9, 15), (11, 16)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A two-colour certificate for a two-fold Langford sequence of order 4 and defect 6. -/
theorem twoFold_lit_6_4 : TwoFold 6 4 {(1, 7), (2, 11), (3, 10), (4, 12)} {(5, 13), (6, 15), (8, 14), (9, 16)} := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end L2
