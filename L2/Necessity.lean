import L2.Defs

/-!
# The necessary conditions

For an `m`-fold Langford sequence of order `l` and defect `d`, choose for each difference `p` the set
`A p` of left ends of its `m` pairs. The left ends `L` and the right ends `R` of all `ml` pairs
partition `[1, 2ml]`, and `ΣR − ΣL = m · Σ_{p=d}^{d+l−1} p`. Over any split of `[1, 2ml]` into two
halves of size `ml`, `ΣR − ΣL ≤ (ml)²`; this gives `2d + l ≤ 2ml + 1`. The parity of
`ΣR + ΣL = ml(2ml + 1)` gives, for odd `m`, `l(2d + l + 1) ≡ 0 (mod 4)`.
-/

namespace L2

namespace Nec

/-- A `k`-subset of `[1, N]` has sum at most that of the top `k` elements: `2·ΣR ≤ k(2N + 1 − k)`. -/
theorem sum_le_top (R : Finset ℕ) (N : ℕ) (hR : ∀ x ∈ R, 1 ≤ x ∧ x ≤ N) :
    2 * ∑ x ∈ R, x ≤ R.card * (2 * N + 1 - R.card) := by
  sorry

/-- A `k`-subset of the positive integers has sum at least that of `[1, k]`: `2·ΣL ≥ k(k + 1)`. -/
theorem bottom_le_sum (L : Finset ℕ) (hL : ∀ x ∈ L, 1 ≤ x) :
    L.card * (L.card + 1) ≤ 2 * ∑ x ∈ L, x := by
  sorry

/-- The sum of the differences: `2 · Σ_{p=d}^{d+l−1} p = l(2d + l − 1)`. -/
theorem sum_Icc_d (d l : ℕ) :
    2 * ∑ p ∈ Finset.Icc d (d + l - 1), p = l * (2 * d + l - 1) := by
  sorry

/-- A choice of the left-end sets `A p`, one for each difference `p ∈ [d, d + l − 1]`, with the
clauses of `Langford.IsLangford`. -/
def Choice (m d l : ℕ) (s : ℕ → ℕ) (A : ℕ → Finset ℕ) : Prop :=
  ∀ p : ℕ, d ≤ p → p < d + l →
    (A p).card = m ∧
      (∀ a ∈ A p, 1 ≤ a ∧ a + p ≤ 2 * m * l ∧ a + p ∉ A p) ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ 2 * m * l → (s i = p ↔ i ∈ A p ∨ ∃ a ∈ A p, i = a + p)

/-- Every Langford sequence admits a choice of left-end sets. -/
theorem exists_choice {m d l : ℕ} {s : ℕ → ℕ} (hs : Langford.IsLangford m d l s) :
    ∃ A : ℕ → Finset ℕ, Choice m d l s A := by
  sorry

/-- The left ends of all pairs. -/
def leftEnds (d l : ℕ) (A : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.Icc d (d + l - 1)).biUnion A

/-- The right ends of all pairs. -/
def rightEnds (d l : ℕ) (A : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.Icc d (d + l - 1)).biUnion fun p => (A p).image (· + p)

/-- No position is both a left end and a right end. -/
theorem left_right_disjoint {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hd : 1 ≤ d) (hl : 1 ≤ l)
    (hs : Langford.IsLangford m d l s) (hA : Choice m d l s A) :
    Disjoint (leftEnds d l A) (rightEnds d l A) := by
  sorry

/-- The left ends and the right ends together are the positions `[1, 2ml]`. -/
theorem left_right_union {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hd : 1 ≤ d) (hl : 1 ≤ l)
    (hs : Langford.IsLangford m d l s) (hA : Choice m d l s A) :
    leftEnds d l A ∪ rightEnds d l A = Finset.Icc 1 (2 * m * l) := by
  sorry

/-- There are `ml` left ends. -/
theorem card_left {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hd : 1 ≤ d) (hl : 1 ≤ l)
    (hs : Langford.IsLangford m d l s) (hA : Choice m d l s A) :
    (leftEnds d l A).card = m * l := by
  sorry

/-- There are `ml` right ends. -/
theorem card_right {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hd : 1 ≤ d) (hl : 1 ≤ l)
    (hs : Langford.IsLangford m d l s) (hA : Choice m d l s A) :
    (rightEnds d l A).card = m * l := by
  sorry

/-- The distance sum: `ΣR = ΣL + m · Σ_{p=d}^{d+l−1} p`. -/
theorem sum_right_sub_left {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hd : 1 ≤ d) (hl : 1 ≤ l)
    (hs : Langford.IsLangford m d l s) (hA : Choice m d l s A) :
    ∑ x ∈ rightEnds d l A, x =
      ∑ x ∈ leftEnds d l A, x + m * ∑ p ∈ Finset.Icc d (d + l - 1), p := by
  sorry

end Nec

/-- Every `m`-fold Langford sequence (`m, d, l ≥ 1`) satisfies `(2m − 1)l ≥ 2d − 1`, and for odd `m`
also `l(2d + l + 1) ≡ 0 (mod 4)`. -/
theorem necessary_internal (m d l : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (s : ℕ → ℕ)
    (hs : Langford.IsLangford m d l s) :
    2 * d + l ≤ 2 * m * l + 1 ∧ (m % 2 = 1 → l * (2 * d + l + 1) % 4 = 0) := by
  sorry

end L2
