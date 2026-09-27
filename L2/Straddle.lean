import L2.Necessity

/-!
# Rigidity of the counting bound

Equality `2d + l = 2ml + 1` in the counting bound holds exactly when every pair straddles the midpoint: every
position `i ≤ ml` is the left end of its pair, `ml < i + s i`. If the left ends are `[1, ml]` and the right ends
`[ml + 1, 2ml]`, the distance sum is `(ml)²`, which is the equality case; conversely the extremal sums are rigid — a
set of `ml` positive integers with the sum of `[1, ml]` is `[1, ml]` — so equality forces the left ends to be
`[1, ml]`, and then every position `i ≤ ml` pairs to the right of `ml`.
-/

namespace L2

namespace Str

/-- A finite set of positive integers with an element above its cardinality has sum strictly larger than that of
`[1, k]`, `k` its cardinality. -/
theorem bottom_lt_sum (L : Finset ℕ) (hL : ∀ x ∈ L, 1 ≤ x) (hx : ∃ x ∈ L, L.card < x) :
    L.card * (L.card + 1) < 2 * ∑ x ∈ L, x := by
  sorry

/-- A finite set of `k` positive integers with the sum of `[1, k]` is `[1, k]`. -/
theorem bottom_eq (L : Finset ℕ) (hL : ∀ x ∈ L, 1 ≤ x) (hsum : 2 * ∑ x ∈ L, x = L.card * (L.card + 1)) :
    L = Finset.Icc 1 L.card := by
  sorry

end Str

/-- Equality in the counting bound is rigid: `2d + l = 2ml + 1` if and only if every position `i ≤ ml` is the left end
of its pair, that is `ml < i + s i`. -/
theorem tight_iff_straddle_internal (m d l : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (s : ℕ → ℕ)
    (hs : Langford.IsLangford m d l s) :
    2 * d + l = 2 * m * l + 1 ↔ ∀ i : ℕ, 1 ≤ i → i ≤ m * l → m * l < i + s i := by
  sorry

end L2
