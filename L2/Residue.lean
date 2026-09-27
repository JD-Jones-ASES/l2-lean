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
  have h4 : (0 : ℤ) < 4 * T := by omega
  have hu0 : 0 ≤ y % (4 * T) := Int.emod_nonneg y (by omega)
  have hu1 : y % (4 * T) < 4 * T := Int.emod_lt_of_pos y h4
  have e1 : (y + 2 * T) % (4 * T) = (y % (4 * T) + 2 * T) % (4 * T) := by
    rw [Int.add_emod, Int.emod_eq_of_lt (a := 2 * T) (by omega) (by omega)]
  unfold tri
  rw [e1]
  by_cases h : y % (4 * T) < 2 * T
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · have e2 : y % (4 * T) + 2 * T = (y % (4 * T) - 2 * T) + 4 * T := by ring
    rw [e2, Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- The wave is even. -/
theorem tri_neg {T : ℤ} (hT : 0 < T) (y : ℤ) : tri T (-y) = tri T y := by
  have h4 : (0 : ℤ) < 4 * T := by omega
  have hu0 : 0 ≤ y % (4 * T) := Int.emod_nonneg y (by omega)
  have hu1 : y % (4 * T) < 4 * T := Int.emod_lt_of_pos y h4
  have e1 : (-y) % (4 * T) = (4 * T - y % (4 * T)) % (4 * T) := by
    have h := Int.emod_add_mul_ediv y (4 * T)
    have e : -y = (4 * T - y % (4 * T)) + (-(y / (4 * T)) - 1) * (4 * T) := by
      linear_combination h
    rw [e, Int.add_mul_emod_self_right]
  unfold tri
  rw [e1]
  rcases eq_or_lt_of_le hu0 with h | h
  · have h' : 4 * T - y % (4 * T) = 4 * T := by omega
    rw [h', Int.emod_self]
    omega
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- One step moves the wave by at most `1`. -/
theorem tri_succ {T : ℤ} (hT : 0 < T) (y : ℤ) : |tri T (y + 1) - tri T y| ≤ 1 := by
  have h4 : (0 : ℤ) < 4 * T := by omega
  have hu0 : 0 ≤ y % (4 * T) := Int.emod_nonneg y (by omega)
  have hu1 : y % (4 * T) < 4 * T := Int.emod_lt_of_pos y h4
  have e1 : (y + 1) % (4 * T) = (y % (4 * T) + 1) % (4 * T) := by
    rw [Int.add_emod, Int.emod_eq_of_lt (a := 1) (by omega) (by omega)]
  unfold tri
  rw [e1, abs_le]
  by_cases h : y % (4 * T) + 1 < 4 * T
  · rw [Int.emod_eq_of_lt (by omega) h]
    constructor <;> omega
  · have e2 : y % (4 * T) + 1 = 4 * T := by omega
    rw [e2, Int.emod_self]
    constructor <;> omega

/-- The wave has Lipschitz constant `1`. -/
theorem tri_lipschitz {T : ℤ} (hT : 0 < T) (y h : ℤ) : |tri T (y + h) - tri T y| ≤ |h| := by
  have key : ∀ k : ℕ, ∀ z : ℤ, |tri T (z + k) - tri T z| ≤ k := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      have h1 := tri_succ hT (z + k)
      have h2 := ih z
      have e : z + ((k + 1 : ℕ) : ℤ) = z + k + 1 := by push_cast; ring
      rw [e]
      calc |tri T (z + k + 1) - tri T z|
          ≤ |tri T (z + k + 1) - tri T (z + k)| + |tri T (z + k) - tri T z| := abs_sub_le _ _ _
        _ ≤ 1 + k := by linarith
        _ = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg h
  · rw [Nat.abs_cast k]
    exact key k y
  · rw [abs_neg, Nat.abs_cast k, abs_sub_comm]
    have := key k (y + -(k : ℤ))
    rwa [show y + -(k : ℤ) + (k : ℤ) = y by ring] at this

/-- On `[0, 2T]` the wave is `T − y`. -/
theorem tri_eq {T : ℤ} (hT : 0 < T) {y : ℤ} (h0 : 0 ≤ y) (h1 : y ≤ 2 * T) : tri T y = T - y := by
  unfold tri
  rw [Int.emod_eq_of_lt h0 (by omega)]
  omega

/-- The sum of the wave at the first `r ≤ T` odd numbers is `r(T − r)`. -/
theorem sum_tri_lt {T : ℤ} (hT : 0 < T) (r : ℕ) (hr : (r : ℤ) ≤ T) :
    ∑ k ∈ Finset.range r, tri T (2 * (k : ℤ) + 1) = r * (T - r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih (by omega), tri_eq hT (by omega) (by omega)]
    push_cast
    ring

/-- The sum of the wave at the first `T + N` odd numbers is minus its sum at the first `N`: the first block of `T`
sums to zero, and the antiperiod negates every later term. -/
theorem sum_tri_add {t : ℕ} (ht : 0 < (t : ℤ)) (N : ℕ) :
    ∑ k ∈ Finset.range (t + N), tri (t : ℤ) (2 * (k : ℤ) + 1) =
      - ∑ k ∈ Finset.range N, tri (t : ℤ) (2 * (k : ℤ) + 1) := by
  rw [Finset.sum_range_add, sum_tri_lt ht t le_rfl, sub_self, mul_zero, zero_add,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← tri_add_two_mul ht]
  congr 1
  push_cast
  ring

/-- The sum of the wave at the first `n` odd numbers is `(−1)^q r(T − r)` where `n = qT + r`, `0 ≤ r < T`. -/
theorem sum_tri_mod {T : ℤ} (hT : 0 < T) (n : ℕ) :
    ∑ k ∈ Finset.range n, tri T (2 * (k : ℤ) + 1) =
      (-1) ^ (n / T.toNat) * (((n : ℤ) % T) * (T - (n : ℤ) % T)) := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, T = t := ⟨T.toNat, (Int.toNat_of_nonneg hT.le).symm⟩
  rw [Int.toNat_natCast, ← Int.natCast_emod]
  have ht : 0 < t := by omega
  have key : ∀ q r : ℕ, r ≤ t → ∑ k ∈ Finset.range (q * t + r), tri (t : ℤ) (2 * (k : ℤ) + 1) =
      (-1) ^ q * ((r : ℤ) * ((t : ℤ) - r)) := by
    intro q r hr
    induction q with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, pow_zero, one_mul]
      exact sum_tri_lt hT r (by omega)
    | succ q ih =>
      rw [show (q + 1) * t + r = t + (q * t + r) by ring, sum_tri_add hT, ih, pow_succ]
      ring
  conv_lhs => rw [← Nat.div_add_mod' n t]
  exact key _ _ (Nat.mod_lt n ht).le

/-- A sum over `[1, N]` is a sum over `range N` shifted by one. -/
theorem sum_Icc_one (f : ℕ → ℤ) (N : ℕ) :
    ∑ x ∈ Finset.Icc 1 N, f x = ∑ k ∈ Finset.range N, f (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- The sum of the centred wave over the positions `1, …, 2n` is twice the sum at the first `n` odd numbers. -/
theorem sum_positions {T : ℤ} (hT : 0 < T) (n : ℕ) :
    ∑ x ∈ Finset.Icc 1 (2 * n), tri T (2 * (x : ℤ) - 2 * n - 1) =
      2 * ∑ k ∈ Finset.range n, tri T (2 * (k : ℤ) + 1) := by
  rw [sum_Icc_one (fun x => tri T (2 * (x : ℤ) - 2 * n - 1)), two_mul n, Finset.sum_range_add,
    two_mul (∑ k ∈ Finset.range n, tri T (2 * (k : ℤ) + 1))]
  congr 1
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [← tri_neg hT (2 * (j : ℤ) + 1)]
    congr 1
    omega
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    push_cast
    ring

/-- The edge inequality: for either sign, a pair `{a, a + p}` costs at most `2|p − T|` against the centred wave. -/
theorem edge {T : ℤ} (hT : 0 < T) (n a p : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    0 ≤ σ * (tri T (2 * (a : ℤ) - 2 * n - 1) + tri T (2 * ((a + p : ℕ) : ℤ) - 2 * n - 1)) +
      2 * |(p : ℤ) - T| := by
  have e1 : 2 * ((a + p : ℕ) : ℤ) - 2 * n - 1 =
      ((2 * (a : ℤ) - 2 * n - 1) + 2 * ((p : ℤ) - T)) + 2 * T := by
    push_cast
    ring
  rw [e1, tri_add_two_mul hT]
  have hL := tri_lipschitz hT (2 * (a : ℤ) - 2 * n - 1) (2 * ((p : ℤ) - T))
  rw [abs_mul, abs_two] at hL
  rcases abs_le.1 hL with ⟨h1, h2⟩
  rcases hσ with rfl | rfl <;> linarith

/-- A weight summed over the left ends is the sum over the differences of its sum over the left-end sets. -/
theorem sum_left_weighted {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hl : 1 ≤ l)
    (hA : Nec.Choice m d l s A) (w : ℕ → ℤ) :
    ∑ x ∈ Nec.leftEnds d l A, w x = ∑ p ∈ Finset.Icc d (d + l - 1), ∑ a ∈ A p, w a := by
  unfold Nec.leftEnds
  rw [Finset.sum_biUnion (Nec.pairwise_left hl hA)]

/-- A weight summed over the right ends is the sum over the differences of its sum over the translated
left-end sets. -/
theorem sum_right_weighted {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hl : 1 ≤ l)
    (hA : Nec.Choice m d l s A) (w : ℕ → ℤ) :
    ∑ x ∈ Nec.rightEnds d l A, w x = ∑ p ∈ Finset.Icc d (d + l - 1), ∑ a ∈ A p, w (a + p) := by
  unfold Nec.rightEnds
  rw [Finset.sum_biUnion (Nec.pairwise_right hl hA)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_image (fun a _ b _ h => add_right_cancel h)]

/-- A sum over the window of differences `[d, d + l − 1]` is a sum over `p = d + i`, `i < l`. -/
theorem sum_window (f : ℕ → ℤ) (d l : ℕ) (hl : 1 ≤ l) :
    ∑ p ∈ Finset.Icc d (d + l - 1), f p = ∑ i ∈ Finset.range l, f (d + i) := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  rw [show d + (k + 1) - 1 = d + k by omega]
  clear hl
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ _ (k + 1), ← ih, ← add_assoc, Finset.sum_Icc_succ_top (by omega)]

/-- `2 · Σ_{i=0}^{u} |i − u| = u(u + 1)`, the distance written with truncated subtraction. -/
theorem sum_dist_low (u : ℕ) : 2 * ∑ i ∈ Finset.range (u + 1), ((i - u) + (u - i)) = u * (u + 1) := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Finset.sum_range_succ', Finset.sum_congr rfl fun i _ =>
      (show (i + 1 - (u + 1)) + ((u + 1) - (i + 1)) = (i - u) + (u - i) by omega), mul_add, ih]
    simp only [Nat.zero_sub, Nat.sub_zero, zero_add]
    ring

/-- `2 · Σ_{i=0}^{u+v} |i − u| = u(u + 1) + v(v + 1)`, the distance written with truncated subtraction. -/
theorem sum_dist_high (u v : ℕ) :
    2 * ∑ i ∈ Finset.range (u + 1 + v), ((i - u) + (u - i)) = u * (u + 1) + v * (v + 1) := by
  induction v with
  | zero => simpa using sum_dist_low u
  | succ v ih =>
    rw [← add_assoc, Finset.sum_range_succ, mul_add, ih]
    have e : u + 1 + v - u + (u - (u + 1 + v)) = v + 1 := by omega
    rw [e]
    ring

end Res

set_option linter.unusedVariables false in
/-- The residue bound: for every `T ≥ 1`, with `r = ml mod T`, `r(T − r) ≤ m · Σ_{p=d}^{d+l−1} |p − T|`; the distance
`|p − T|` is written with truncated subtraction as `(p − T) + (T − p)`, `p = d + i`. -/
theorem residue_bound_internal (m d l T : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (hT : 1 ≤ T) (s : ℕ → ℕ)
    (hs : Langford.IsLangford m d l s) :
    (m * l % T) * (T - m * l % T) ≤ m * ∑ i ∈ Finset.range l, ((d + i - T) + (T - (d + i))) := by
  obtain ⟨A, hA⟩ := Nec.exists_choice hs
  have hdisj : Disjoint (Nec.leftEnds d l A) (Nec.rightEnds d l A) := Nec.left_right_disjoint hd hl hs hA
  have hunion : Nec.leftEnds d l A ∪ Nec.rightEnds d l A = Finset.Icc 1 (2 * m * l) :=
    Nec.left_right_union hd hl hs hA
  have hTz : (0 : ℤ) < (T : ℤ) := by omega
  obtain ⟨n, hn⟩ : ∃ n, n = m * l := ⟨_, rfl⟩
  rw [← hn]
  have e2n : 2 * n = 2 * m * l := by rw [hn]; ring
  -- the centred wave on the positions
  obtain ⟨V, hV⟩ : ∃ V : ℕ → ℤ, V = fun x : ℕ => Res.tri (T : ℤ) (2 * (x : ℤ) - 2 * (n : ℤ) - 1) :=
    ⟨_, rfl⟩
  -- the positions are the endpoints of the pairs
  have hpairs : ∑ x ∈ Finset.Icc 1 (2 * n), V x =
      ∑ p ∈ Finset.Icc d (d + l - 1), ∑ a ∈ A p, (V a + V (a + p)) := by
    rw [e2n, ← hunion, Finset.sum_union hdisj, Res.sum_left_weighted hl hA V,
      Res.sum_right_weighted hl hA V, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_add_distrib]
  -- the sum of the wave over the positions
  have htotal : ∑ x ∈ Finset.Icc 1 (2 * n), V x =
      2 * ((-1) ^ (n / (T : ℤ).toNat) * (((n : ℤ) % T) * ((T : ℤ) - (n : ℤ) % T))) := by
    rw [hV, ← Res.sum_tri_mod hTz n]
    exact Res.sum_positions hTz n
  -- the sign that makes the position sum negative
  obtain ⟨σ, hσ, hσ2⟩ : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ σ * (-1) ^ (n / (T : ℤ).toNat) = -1 := by
    rcases neg_one_pow_eq_or ℤ (n / (T : ℤ).toNat) with h | h
    · exact ⟨-1, Or.inr rfl, by rw [h]; norm_num⟩
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
  -- the edge inequality, summed over the pairs
  have hedge : 0 ≤ ∑ p ∈ Finset.Icc d (d + l - 1),
      ∑ a ∈ A p, (σ * (V a + V (a + p)) + 2 * |(p : ℤ) - T|) := by
    apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro a _
    have h := Res.edge hTz n a p σ hσ
    rw [hV]
    exact h
  have hsplit : ∑ p ∈ Finset.Icc d (d + l - 1),
      ∑ a ∈ A p, (σ * (V a + V (a + p)) + 2 * |(p : ℤ) - T|) =
      σ * ∑ x ∈ Finset.Icc 1 (2 * n), V x + 2 * m * ∑ p ∈ Finset.Icc d (d + l - 1), |(p : ℤ) - T| := by
    rw [hpairs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
      (hA p (Nec.mem_window hl hp).1 (Nec.mem_window hl hp).2).1, nsmul_eq_mul]
    ring
  -- the bound over the integers
  have hZ : (n : ℤ) % T * ((T : ℤ) - (n : ℤ) % T) ≤
      (m : ℤ) * ∑ p ∈ Finset.Icc d (d + l - 1), |(p : ℤ) - T| := by
    have h1 := hedge
    rw [hsplit, htotal] at h1
    have h3 : σ * (2 * ((-1) ^ (n / (T : ℤ).toNat) * ((n : ℤ) % T * ((T : ℤ) - (n : ℤ) % T)))) =
        -2 * ((n : ℤ) % T * ((T : ℤ) - (n : ℤ) % T)) := by
      linear_combination (2 * ((n : ℤ) % T * ((T : ℤ) - (n : ℤ) % T))) * hσ2
    rw [h3] at h1
    linarith
  -- back to the natural numbers
  have hwin : ∑ p ∈ Finset.Icc d (d + l - 1), |(p : ℤ) - T| =
      ∑ i ∈ Finset.range l, (((d + i - T) + (T - (d + i)) : ℕ) : ℤ) := by
    rw [Res.sum_window _ d l hl]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total (d + i) T with h | h
    · rw [abs_of_nonpos (by omega)]
      omega
    · rw [abs_of_nonneg (by omega)]
      omega
  have hlt : n % T < T := Nat.mod_lt n (by omega)
  have final : ((n % T * (T - n % T) : ℕ) : ℤ) ≤
      ((m * ∑ i ∈ Finset.range l, ((d + i - T) + (T - (d + i))) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sum, Nat.cast_sub hlt.le, Int.natCast_emod, ← hwin]
    exact hZ
  exact_mod_cast final

set_option linter.unusedVariables false in
/-- The residue bound in the window `d ≤ T ≤ d + l − 1`, where `2 · Σ_p |p − T| = u(u + 1) + v(v + 1)` with
`u = T − d` and `v = d + l − 1 − T`. -/
theorem residue_bound_window (m d l T : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (hT1 : d ≤ T)
    (hT2 : T < d + l) (s : ℕ → ℕ) (hs : Langford.IsLangford m d l s) :
    2 * (m * l % T) * (T - m * l % T) ≤ m * ((T - d) * (T - d + 1) + (d + l - 1 - T) * (d + l - T)) := by
  have hmain := residue_bound_internal m d l T hm hd hl (by omega) s hs
  obtain ⟨u, rfl⟩ : ∃ u, T = d + u := ⟨T - d, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, l = u + 1 + v := ⟨l - u - 1, by omega⟩
  have hS := Res.sum_dist_high u v
  have hsum : ∑ i ∈ Finset.range (u + 1 + v), ((d + i - (d + u)) + ((d + u) - (d + i))) =
      ∑ i ∈ Finset.range (u + 1 + v), ((i - u) + (u - i)) :=
    Finset.sum_congr rfl fun i _ => by omega
  rw [hsum] at hmain
  have e1 : d + u - d = u := by omega
  have e2 : d + (u + 1 + v) - 1 - (d + u) = v := by omega
  have e3 : d + (u + 1 + v) - (d + u) = v + 1 := by omega
  rw [e1, e2, e3, ← hS]
  calc 2 * (m * (u + 1 + v) % (d + u)) * (d + u - m * (u + 1 + v) % (d + u))
      = 2 * ((m * (u + 1 + v) % (d + u)) * (d + u - m * (u + 1 + v) % (d + u))) := by
        rw [Nat.mul_assoc]
    _ ≤ 2 * (m * ∑ i ∈ Finset.range (u + 1 + v), ((i - u) + (u - i))) := Nat.mul_le_mul_left 2 hmain
    _ = m * (2 * ∑ i ∈ Finset.range (u + 1 + v), ((i - u) + (u - i))) := by ring

end L2
