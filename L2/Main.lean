import L2.Cone
import L2.LemmaS
import L2.Bridge
import L2.Tight
import L2.Necessity
import L2.OrderOne
import L2.SixThree
import L2.Literals

/-!
# The theorems

Every cell `(d, l)` with `2d ≤ 3l + 1` has a two-colour certificate, by strong induction on `l`: the
cells with `l ≤ 4` are literal; a cell with `l ≥ 2d` is the concatenation of `(d, l₁)` and
`(d + l₁, l − l₁)` with `l₁ = ⌊(2d + 1)/3⌋`; every other cell with `l ≥ 5` comes from a solution of
`SP(l, d − l)` on the cone. With the bridge to sequences and the necessary conditions this gives the
characterisation of two-fold Langford sequences, and the tight line, the row of order one and the
cell `(6, 3)` give the statements for every multiplicity.
-/

namespace L2

/-- Every cell `(d, l)` with `d, l ≥ 1` and `2d ≤ 3l + 1` has a two-colour certificate. -/
theorem twoFold_all (d l : ℕ) (hd : 1 ≤ d) (hl : 1 ≤ l) (h : 2 * d ≤ 3 * l + 1) :
    ∃ A B, TwoFold (d : ℤ) (l : ℤ) A B := by
  induction l using Nat.strong_induction_on generalizing d with
  | _ l ih =>
  by_cases hl4 : l ≤ 4
  · -- the sixteen literal cells
    obtain rfl | rfl | rfl | rfl : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 := by omega
    · obtain rfl | rfl : d = 1 ∨ d = 2 := by omega
      · exact ⟨_, _, twoFold_lit_1_1⟩
      · exact ⟨_, _, twoFold_lit_2_1⟩
    · obtain rfl | rfl | rfl : d = 1 ∨ d = 2 ∨ d = 3 := by omega
      · exact ⟨_, _, twoFold_lit_1_2⟩
      · exact ⟨_, _, twoFold_lit_2_2⟩
      · exact ⟨_, _, twoFold_lit_3_2⟩
    · obtain rfl | rfl | rfl | rfl | rfl : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
      · exact ⟨_, _, twoFold_lit_1_3⟩
      · exact ⟨_, _, twoFold_lit_2_3⟩
      · exact ⟨_, _, twoFold_lit_3_3⟩
      · exact ⟨_, _, twoFold_lit_4_3⟩
      · exact ⟨_, _, twoFold_lit_5_3⟩
    · obtain rfl | rfl | rfl | rfl | rfl | rfl :
          d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
      · exact ⟨_, _, twoFold_lit_1_4⟩
      · exact ⟨_, _, twoFold_lit_2_4⟩
      · exact ⟨_, _, twoFold_lit_3_4⟩
      · exact ⟨_, _, twoFold_lit_4_4⟩
      · exact ⟨_, _, twoFold_lit_5_4⟩
      · exact ⟨_, _, twoFold_lit_6_4⟩
  by_cases hsp : l ≤ 2 * d - 1
  · -- Lemma S on the cone, `δ = d − l`
    obtain ⟨G, hG⟩ := cone_sp (l : ℤ) ((d : ℤ) - l) (by omega) (by omega) (by omega)
    have t := hG.toTwoFold (by omega)
    rw [show (l : ℤ) + ((d : ℤ) - l) = d by ring] at t
    exact ⟨_, _, t⟩
  · -- concatenation of `(d, l₁)` and `(d + l₁, l − l₁)`, `l₁ = ⌊(2d + 1)/3⌋`
    obtain ⟨l₁, hl₁⟩ : ∃ l₁, l₁ = (2 * d + 1) / 3 := ⟨_, rfl⟩
    obtain ⟨A₁, B₁, h₁⟩ := ih l₁ (by omega) d hd (by omega) (by omega)
    obtain ⟨A₂, B₂, h₂⟩ := ih (l - l₁) (by omega) (d + l₁) (by omega) (by omega) (by omega)
    push_cast [Nat.cast_sub (show l₁ ≤ l by omega)] at h₂
    have c := h₁.concat h₂
    rw [show (l₁ : ℤ) + ((l : ℤ) - l₁) = l by ring] at c
    exact ⟨_, _, c⟩

/-- For `d, l ≥ 1`, a two-fold Langford sequence of order `l` and defect `d` exists if and only if
`3l ≥ 2d − 1`. -/
theorem twoFold_exists_iff_internal (d l : ℕ) (hd : 1 ≤ d) (hl : 1 ≤ l) :
    (∃ s : ℕ → ℕ, Langford.IsLangford 2 d l s) ↔ 2 * d ≤ 3 * l + 1 := by
  constructor
  · rintro ⟨s, hs⟩
    have h := (necessary_internal 2 d l (by norm_num) hd hl s hs).1
    omega
  · intro h
    obtain ⟨A, B, hAB⟩ := twoFold_all d l hd hl h
    exact ⟨_, hAB.toMulti.isLangford⟩

/-- If `2d + l = 2ml + 1`, an `m`-fold Langford sequence of order `l` and defect `d` exists. -/
theorem tight_exists_internal (m d l : ℕ) (hm : 1 ≤ m) (h : 2 * d + l = 2 * m * l + 1) :
    ∃ s : ℕ → ℕ, Langford.IsLangford m d l s := by
  rw [show 2 * m * l = 2 * (m * l) by ring] at h
  have hodd : l % 2 = 1 := by omega
  have hZ : 2 * (d : ℤ) + l = 2 * ((m : ℤ) * l) + 1 := by exact_mod_cast h
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : ℤ, 2 * d₀ - 1 = l := ⟨((l : ℤ) + 1) / 2, by omega⟩
  have t := tight_multi m d₀ hm (by omega)
  rw [hd₀] at t
  rw [show (m : ℤ) * l - (d₀ - 1) = d by omega] at t
  exact ⟨_, t.isLangford⟩

end L2
