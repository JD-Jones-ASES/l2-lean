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
  sorry

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
  sorry

end L2
