import L2.Necessity
import L2.Tight
import L2.Bridge
import L2.SixThree

/-!
# The row of order one, and the negative theorem

With one difference `d`, the positions `1, …, 2m` split into blocks of length `d` that alternate
between left ends and right ends, so `2d` divides `2m`; conversely `m / d` copies of the tight
cell `(d, 1)` at multiplicity `d`, side by side, form an `m`-fold sequence. Hence an `m`-fold
Langford sequence of order `1` and defect `d` exists exactly when `d ∣ m`. For `m ≥ 3` this gives
cells that satisfy the necessary conditions and admit no sequence: `(m − 1, 1)` for even `m`,
`(m − 2, 1)` for odd `m ≥ 5`, and `(6, 3)` for `m = 3`.
-/

namespace L2

set_option linter.unusedVariables false in
/-- Necessity on the row of order one: the blocks `[1, d], [d + 1, 2d], …` alternate left ends and
right ends, so `2m` is a multiple of `2d`. -/
theorem dvd_of_order_one (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (s : ℕ → ℕ)
    (hs : Langford.IsLangford m d 1 s) : d ∣ m := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨A, -, hA, hcov⟩ := hs2 d le_rfl (by omega)
  -- Every position carries the one difference `d`, so it is a left end or a right end.
  have cover : ∀ x, 1 ≤ x → x ≤ 2 * m → x ∈ A ∨ ∃ a ∈ A, x = a + d := by
    intro x h1 h2
    have := hs1 x h1 (by omega)
    exact (hcov x h1 (by omega)).mp (by omega)
  have F1 : ∀ x, 1 ≤ x → x ≤ 2 * m → x ≤ d → x ∈ A := by
    intro x h1 h2 h3
    rcases cover x h1 h2 with h | ⟨a, ha, rfl⟩
    · exact h
    · have := (hA a ha).1
      omega
  have F2 : ∀ x, d < x → x ≤ 2 * m → x - d ∉ A → x ∈ A := by
    intro x h1 h2 h3
    rcases cover x (by omega) h2 with h | ⟨a, ha, rfl⟩
    · exact h
    · exact absurd (by rwa [Nat.add_sub_cancel]) h3
  have F3 : ∀ a ∈ A, a + d ∉ A := fun a ha => (hA a ha).2.2
  have mem_congr : ∀ {x y : ℕ}, x = y → x ∈ A → y ∈ A := fun h hx => h ▸ hx
  -- The alternating blocks: `[2dq + 1, 2dq + d]` are left ends, `[2dq + d + 1, 2dq + 2d]` are not.
  have P : ∀ q : ℕ, ∀ r < d, (2 * (d * q) + r + 1 ≤ 2 * m → 2 * (d * q) + r + 1 ∈ A) ∧
      (2 * (d * q) + d + r + 1 ≤ 2 * m → 2 * (d * q) + d + r + 1 ∉ A) := by
    intro q
    induction q with
    | zero =>
      intro r hr
      have h1 : 2 * (d * 0) + r + 1 ≤ 2 * m → 2 * (d * 0) + r + 1 ∈ A := fun h =>
        F1 _ (by omega) h (by omega)
      refine ⟨h1, fun h hx => ?_⟩
      exact F3 _ (h1 (by omega)) (mem_congr (by omega) hx)
    | succ q ih =>
      intro r hr
      have h1 : 2 * (d * (q + 1)) + r + 1 ≤ 2 * m → 2 * (d * (q + 1)) + r + 1 ∈ A := by
        intro h
        rw [Nat.mul_succ] at h ⊢
        refine F2 _ (by omega) h fun hx => (ih r hr).2 (by omega) (mem_congr (by omega) hx)
      refine ⟨h1, fun h hx => ?_⟩
      rw [Nat.mul_succ] at h hx h1
      exact F3 _ (h1 (by omega)) (mem_congr (by omega) hx)
  -- The last block is complete: `2m = 2dQ + R` with `R = 0`.
  obtain ⟨Q, R, hR, hQR⟩ : ∃ Q R, R < 2 * d ∧ 2 * m = 2 * (d * Q) + R := by
    refine ⟨2 * m / (2 * d), 2 * m % (2 * d), Nat.mod_lt _ (by omega), ?_⟩
    have := Nat.div_add_mod (2 * m) (2 * d)
    rw [mul_assoc] at this
    omega
  by_cases hR0 : R = 0
  · exact ⟨Q, by omega⟩
  · exfalso
    have hx := (P Q (min R d - 1) (by omega)).1 (by omega)
    have := (hA _ hx).2.1
    omega

/-- Sufficiency on the row of order one: `m / d` juxtaposed copies of the tight cell `(d, 1)` at
multiplicity `d`. -/
theorem order_one_of_dvd (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (h : d ∣ m) :
    ∃ s : ℕ → ℕ, Langford.IsLangford m d 1 s := by
  obtain ⟨k, rfl⟩ := h
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      simp at hm
    · exact h
  -- The tight cell `(d, 1)` at multiplicity `d`.
  have h0 : MultiPairing d (d : ℤ) 1 (tightColour d 1) := by
    have h := tight_multi d 1 hd le_rfl
    have e1 : ((d : ℤ) * (2 * 1 - 1) - (1 - 1)) = d := by ring
    have e2 : ((2 : ℤ) * 1 - 1) = 1 := by norm_num
    rw [e1, e2] at h
    exact h
  -- `k` copies side by side.
  have key : ∀ k, 1 ≤ k → ∃ C, MultiPairing (d * k) (d : ℤ) 1 C := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact ⟨_, by rw [Nat.mul_one]; exact h0⟩
    | succ k _ ih =>
      obtain ⟨C, hC⟩ := ih
      exact ⟨_, by rw [Nat.mul_succ]; exact hC.juxtapose h0⟩
  obtain ⟨C, hC⟩ := key k hk
  exact ⟨toSeq (d * k) C, MultiPairing.isLangford (by exact_mod_cast hC)⟩

/-- An `m`-fold Langford sequence of order `1` and defect `d` exists if and only if `d ∣ m`. -/
theorem order_one_iff_internal (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    (∃ s : ℕ → ℕ, Langford.IsLangford m d 1 s) ↔ d ∣ m :=
  ⟨fun ⟨s, hs⟩ => dvd_of_order_one m d hm hd s hs, order_one_of_dvd m d hm hd⟩

/-- For every `m ≥ 3` the necessary conditions are not sufficient. -/
theorem not_sufficient_internal (m : ℕ) (hm : 3 ≤ m) :
    ∃ d l : ℕ, 1 ≤ d ∧ 1 ≤ l ∧ 2 * d + l ≤ 2 * m * l + 1 ∧
      (m % 2 = 1 → l * (2 * d + l + 1) % 4 = 0) ∧ ¬ ∃ s : ℕ → ℕ, Langford.IsLangford m d l s := by
  by_cases h3 : m = 3
  · subst h3
    exact ⟨6, 3, by norm_num, by norm_num, by norm_num, fun _ => by norm_num,
      not_threeFold_six_three_internal⟩
  by_cases he : m % 2 = 0
  · -- `m` even: the cell `(m − 1, 1)`, since `m − 1 ∤ m`.
    refine ⟨m - 1, 1, by omega, le_rfl, by omega, fun h => by omega, fun hs => ?_⟩
    have hdvd := (order_one_iff_internal m (m - 1) (by omega) (by omega)).mp hs
    have h1 := Nat.dvd_sub hdvd (dvd_refl (m - 1))
    rw [show m - (m - 1) = 1 by omega] at h1
    have := Nat.le_of_dvd one_pos h1
    omega
  · -- `m` odd, `m ≥ 5`: the cell `(m − 2, 1)`, since `m − 2 ∤ m`.
    refine ⟨m - 2, 1, by omega, le_rfl, by omega, fun _ => by omega, fun hs => ?_⟩
    have hdvd := (order_one_iff_internal m (m - 2) (by omega) (by omega)).mp hs
    have h1 := Nat.dvd_sub hdvd (dvd_refl (m - 2))
    rw [show m - (m - 2) = 2 by omega] at h1
    have := Nat.le_of_dvd two_pos h1
    omega

end L2
