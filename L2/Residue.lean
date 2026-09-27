import L2.Necessity

/-!
# The residue bound

For `T ≥ 1` write `r = ml mod T`. Every `m`-fold Langford sequence of order `l` and defect `d` satisfies
`r(T − r) ≤ m · Σ_{p=d}^{d+l−1} |p − T|`. The proof is a potential on the positions: the triangle wave
`V(x) = T − dist(2x − 2ml − 1, 4TZ)` has antiperiod `T` in `x` and Lipschitz constant `2`, so a pair `{a, a + p}`
has `|V(a) + V(a + p)| ≤ 2|p − T|`, while the sum of `V` over the positions `1, …, 2ml` is `±2r(T − r)`. Summing
the edge inequality over the `ml` pairs with the sign that makes the position sum `−2r(T − r)` gives the bound.
For `T ≥ max(ml, d + l − 1)` the bound is the counting bound; at `l = 1`, `T = d` it says `d ∣ m`.
-/

namespace L2

namespace Res

/-- The triangle wave `T − dist(y, 4TZ)` on the integers, with `dist(y, 4TZ) = min(y mod 4T, 4T − y mod 4T)`;
it takes the value `T` at the multiples of `4T` and `−T` at the odd multiples of `2T`. -/
def tri (T y : ℤ) : ℤ := T - min (y % (4 * T)) (4 * T - y % (4 * T))

/-- Antiperiod `2T`: `tri T (y + 2T) = −tri T y`. -/
theorem tri_add_two_mul {T : ℤ} (hT : 0 < T) (y : ℤ) : tri T (y + 2 * T) = - tri T y := by
  sorry

/-- The wave is even. -/
theorem tri_neg {T : ℤ} (hT : 0 < T) (y : ℤ) : tri T (-y) = tri T y := by
  sorry

/-- The wave has Lipschitz constant `1`. -/
theorem tri_lipschitz {T : ℤ} (hT : 0 < T) (y h : ℤ) : |tri T (y + h) - tri T y| ≤ |h| := by
  sorry

/-- On `[0, 2T]` the wave is `T − y`. -/
theorem tri_eq {T : ℤ} (hT : 0 < T) {y : ℤ} (h0 : 0 ≤ y) (h1 : y ≤ 2 * T) : tri T y = T - y := by
  sorry

/-- The sum of the wave at the first `r ≤ T` odd numbers is `r(T − r)`. -/
theorem sum_tri_lt {T : ℤ} (hT : 0 < T) (r : ℕ) (hr : (r : ℤ) ≤ T) :
    ∑ k ∈ Finset.range r, tri T (2 * (k : ℤ) + 1) = r * (T - r) := by
  sorry

/-- The sum of the wave at the first `n` odd numbers is `(−1)^q r(T − r)` where `n = qT + r`, `0 ≤ r < T`. -/
theorem sum_tri_mod {T : ℤ} (hT : 0 < T) (n : ℕ) :
    ∑ k ∈ Finset.range n, tri T (2 * (k : ℤ) + 1) =
      (-1) ^ (n / T.toNat) * (((n : ℤ) % T) * (T - (n : ℤ) % T)) := by
  sorry

/-- The sum of the centred wave over the positions `1, …, 2n` is twice the sum at the first `n` odd numbers. -/
theorem sum_positions {T : ℤ} (hT : 0 < T) (n : ℕ) :
    ∑ x ∈ Finset.Icc 1 (2 * n), tri T (2 * (x : ℤ) - 2 * n - 1) =
      2 * ∑ k ∈ Finset.range n, tri T (2 * (k : ℤ) + 1) := by
  sorry

/-- The edge inequality: for either sign, a pair `{a, a + p}` costs at most `2|p − T|` against the centred wave. -/
theorem edge {T : ℤ} (hT : 0 < T) (n a p : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    0 ≤ σ * (tri T (2 * (a : ℤ) - 2 * n - 1) + tri T (2 * ((a + p : ℕ) : ℤ) - 2 * n - 1)) +
      2 * |(p : ℤ) - T| := by
  sorry

/-- A weight summed over the left ends is the sum over the differences of its sum over the left-end sets. -/
theorem sum_left_weighted {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hl : 1 ≤ l)
    (hA : Nec.Choice m d l s A) (w : ℕ → ℤ) :
    ∑ x ∈ Nec.leftEnds d l A, w x = ∑ p ∈ Finset.Icc d (d + l - 1), ∑ a ∈ A p, w a := by
  sorry

/-- A weight summed over the right ends is the sum over the differences of its sum over the translated
left-end sets. -/
theorem sum_right_weighted {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hl : 1 ≤ l)
    (hA : Nec.Choice m d l s A) (w : ℕ → ℤ) :
    ∑ x ∈ Nec.rightEnds d l A, w x = ∑ p ∈ Finset.Icc d (d + l - 1), ∑ a ∈ A p, w (a + p) := by
  sorry

end Res

set_option linter.unusedVariables false in
/-- The residue bound: for every `T ≥ 1`, with `r = ml mod T`, `r(T − r) ≤ m · Σ_{p=d}^{d+l−1} |p − T|`; the distance
`|p − T|` is written with truncated subtraction as `(p − T) + (T − p)`, `p = d + i`. -/
theorem residue_bound_internal (m d l T : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (hT : 1 ≤ T) (s : ℕ → ℕ)
    (hs : Langford.IsLangford m d l s) :
    (m * l % T) * (T - m * l % T) ≤ m * ∑ i ∈ Finset.range l, ((d + i - T) + (T - (d + i))) := by
  sorry

set_option linter.unusedVariables false in
/-- The residue bound in the window `d ≤ T ≤ d + l − 1`, where `2 · Σ_p |p − T| = u(u + 1) + v(v + 1)` with
`u = T − d` and `v = d + l − 1 − T`. -/
theorem residue_bound_window (m d l T : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (hT1 : d ≤ T)
    (hT2 : T < d + l) (s : ℕ → ℕ) (hs : Langford.IsLangford m d l s) :
    2 * (m * l % T) * (T - m * l % T) ≤ m * ((T - d) * (T - d + 1) + (d + l - 1 - T) * (d + l - T)) := by
  sorry

end L2
