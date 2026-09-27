import Mathlib

/-!
# The compared definition

The definition of `Challenge.lean`, repeated character for character so that the development can
use it without importing the challenge environment.
-/

namespace Langford

/-- `s` is an `m`-fold Langford sequence of order `l` and defect `d`, read on the positions
`1, …, 2ml`: every entry lies in `[d, d + l − 1]`, and for every `p` in that interval the positions
carrying `p` are exactly the endpoints of `m` pairwise disjoint pairs `{a, a + p}`. -/
def IsLangford (m d l : ℕ) (s : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, 1 ≤ i → i ≤ 2 * m * l → d ≤ s i ∧ s i < d + l) ∧
  ∀ p : ℕ, d ≤ p → p < d + l →
    ∃ A : Finset ℕ, A.card = m ∧
      (∀ a ∈ A, 1 ≤ a ∧ a + p ≤ 2 * m * l ∧ a + p ∉ A) ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ 2 * m * l → (s i = p ↔ i ∈ A ∨ ∃ a ∈ A, i = a + p)

end Langford
