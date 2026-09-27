import L2.Necessity
import L2.SixThree

/-!
# The forced-endpoint bound, the order-three cells and the top of order two

In an `m`-fold Langford sequence the positions `1, …, d` are left ends (a right end `a + p` has `a ≥ 1` and
`p ≥ d`) and every left end is at most `2ml − d`. So the left ends are `[1, d]` together with `ml − d` positions of
`[d + 1, 2ml − d]`, whose sum is at most that of the top `ml − d` of them; the distance sum fixes the sum of the
left ends, and comparing gives `6mld + ml ≤ 4d² + 2(ml)² + ml²`, that is `ml · e ≤ (l − 1 + e)²` for the excess
`e = (2m − 1)l − 2d + 1`. At `(d, l) = (3m − 3, 3)` the excess is `4` and the bound reads `12m ≤ 36`, so for `m ≥ 4`
the cell is empty although it satisfies the counting bound and the parity condition; `m = 3` is the cell `(6, 3)`.
At `(2m − 1, 2)`, the top of the order-two row, the bound reads `2m ≤ 4`.
-/

namespace L2

namespace Frc

/-- The arithmetic of the forced-endpoint bound. Write `H = ml = k + d`, where `k` is the number of left ends
above `d`, and `X = 2d + l − 1`. If the left ends have sum `S` with `4S + HX = 2H(2H + 1)` (the distance sum and
the total sum), and `S = S₁ + S₂` splits it into the sum `S₁` of `[1, d]`, with `2S₁ = d(d + 1)`, and the sum `S₂`
of the `k` left ends above `d`, with `2S₂ ≤ k(3k + 2d + 1)` (at most the top `k` positions of `[1, 2H − d]`), then
`6Hd + H ≤ 4d² + 2H² + Hl`. -/
theorem endpoint_arith (H d l k S S₁ S₂ X : ℕ) (hk : k + d = H) (hX : X + 1 = 2 * d + l)
    (h4 : 4 * S + H * X = 2 * H * (2 * H + 1)) (hS : S = S₁ + S₂) (h₁ : 2 * S₁ = d * (d + 1))
    (h₂ : 2 * S₂ ≤ k * (3 * k + 2 * d + 1)) :
    6 * H * d + H ≤ 4 * d * d + 2 * H * H + H * l := by
  subst hk
  have hX' : (k + d) * (X + 1) = (k + d) * (2 * d + l) := by rw [hX]
  linarith

end Frc

set_option linter.unusedVariables false in
/-- The forced-endpoint bound `6mld + ml ≤ 4d² + 2(ml)² + ml²`. -/
theorem forced_endpoint_internal (m d l : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (s : ℕ → ℕ)
    (hs : Langford.IsLangford m d l s) :
    6 * m * l * d + m * l ≤ 4 * d * d + 2 * (m * l) * (m * l) + m * l * l := by
  have hcount := (necessary_internal m d l hm hd hl s hs).1
  obtain ⟨A, hA⟩ := Nec.exists_choice hs
  set L := Nec.leftEnds d l A with hLdef
  set R := Nec.rightEnds d l A with hRdef
  have hdisj : Disjoint L R := Nec.left_right_disjoint hd hl hs hA
  have hunion : L ∪ R = Finset.Icc 1 (2 * m * l) := Nec.left_right_union hd hl hs hA
  have hcL : L.card = m * l := Nec.card_left hd hl hs hA
  have hsum : ∑ x ∈ R, x = ∑ x ∈ L, x + m * ∑ p ∈ Finset.Icc d (d + l - 1), p :=
    Nec.sum_right_sub_left hd hl hs hA
  have hgap := Nec.sum_Icc_d d l
  -- name the quantities
  set H := m * l with hH
  have h2ml : 2 * m * l = 2 * H := by rw [hH]; ring
  set X := 2 * d + l - 1 with hX
  have hdH : d ≤ H := by
    rw [h2ml] at hcount
    omega
  have hLmem : ∀ x ∈ L, 1 ≤ x := by
    intro x hx
    have : x ∈ L ∪ R := Finset.mem_union_left _ hx
    rw [hunion, Finset.mem_Icc] at this
    exact this.1
  -- the positions `1, …, d` are left ends: a right end `a + p` has `a ≥ 1` and `p ≥ d`
  have hP1 : ∀ x, 1 ≤ x → x ≤ d → x ∈ L := by
    intro x h1 h2
    have hx : x ∈ L ∪ R := by
      rw [hunion, Finset.mem_Icc, h2ml]
      omega
    rcases Finset.mem_union.1 hx with h | h
    · exact h
    · exfalso
      rw [hRdef] at h
      obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.1 h
      obtain ⟨a, ha, hax⟩ := Finset.mem_image.1 hxp
      have hax' : a + p = x := hax
      have hp' := Nec.mem_window hl hp
      have hdp := hp'.1
      have ha1 := ((hA p hp'.1 hp'.2).2.1 a ha).1
      omega
  -- every left end `x` has its partner `x + p ≤ 2ml` with `p ≥ d`
  have hP2 : ∀ x ∈ L, x + d ≤ 2 * H := by
    intro x hx
    rw [hLdef] at hx
    obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.1 hx
    have hp' := Nec.mem_window hl hp
    have hdp := hp'.1
    have h := ((hA p hp'.1 hp'.2).2.1 x hxp).2.1
    rw [h2ml] at h
    omega
  -- the left ends above `d`
  set E := L.filter (fun x => d < x) with hEdef
  have hsplit : L = Finset.Icc 1 d ∪ E := by
    ext x
    simp only [hEdef, Finset.mem_union, Finset.mem_Icc, Finset.mem_filter]
    constructor
    · intro hx
      by_cases h : d < x
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl ⟨hLmem x hx, by omega⟩
    · rintro (⟨h1, h2⟩ | ⟨hx, -⟩)
      · exact hP1 x h1 h2
      · exact hx
  have hdisE : Disjoint (Finset.Icc 1 d) E := by
    rw [Finset.disjoint_left]
    intro x hx hxE
    rw [Finset.mem_Icc] at hx
    rw [hEdef, Finset.mem_filter] at hxE
    omega
  have hcE : E.card + d = H := by
    have h := Finset.card_union_of_disjoint hdisE
    rw [← hsplit, hcL, Nat.card_Icc] at h
    omega
  have hsumE : ∑ x ∈ L, x = ∑ x ∈ Finset.Icc 1 d, x + ∑ x ∈ E, x := by
    rw [hsplit, Finset.sum_union hdisE]
  -- the left ends above `d` lie in `[d + 1, 2ml − d]`: at most the top `ml − d` positions of `[1, 2ml − d]`
  have hEmem : ∀ x ∈ E, 1 ≤ x ∧ x ≤ 2 * H - d := by
    intro x hx
    rw [hEdef, Finset.mem_filter] at hx
    obtain ⟨hxL, hdx⟩ := hx
    have := hP2 x hxL
    omega
  have htopE := Nec.sum_le_top E (2 * H - d) hEmem
  have e1 : 2 * (2 * H - d) + 1 - E.card = 3 * E.card + 2 * d + 1 := by omega
  rw [e1] at htopE
  -- the sum of `[1, d]`
  have hI : 2 * ∑ x ∈ Finset.Icc 1 d, x = d * (d + 1) := by
    have h := Nec.sum_Icc_d 1 d
    have e2 : 1 + d - 1 = d := by omega
    have e3 : 2 * 1 + d - 1 = d + 1 := by omega
    rw [e2, e3] at h
    exact h
  set SL := ∑ x ∈ L, x
  set SR := ∑ x ∈ R, x
  -- the distance sum, doubled
  have hdist : 2 * SR = 2 * SL + H * X := by
    rw [hsum, mul_add, hH, mul_assoc, ← mul_assoc 2 m, mul_comm 2 m, mul_assoc, hgap]
  -- the whole sum
  have hall : 2 * (SL + SR) = 2 * H * (2 * H + 1) := by
    have h1 : SL + SR = ∑ x ∈ Finset.Icc 1 (2 * m * l), x := by
      rw [← hunion, Finset.sum_union hdisj]
    have h2 := Nec.sum_Icc_d 1 (2 * H)
    have e4 : 1 + 2 * H - 1 = 2 * H := by omega
    have e5 : 2 * 1 + 2 * H - 1 = 2 * H + 1 := by omega
    rw [e4, e5] at h2
    rw [h1, h2ml, h2]
  have h4 : 4 * SL + H * X = 2 * H * (2 * H + 1) := by linarith
  have hX1 : X + 1 = 2 * d + l := by omega
  have key := Frc.endpoint_arith H d l E.card SL (∑ x ∈ Finset.Icc 1 d, x) (∑ x ∈ E, x) X hcE hX1 h4
    hsumE hI htopE
  have e6 : 6 * m * l * d = 6 * H * d := by rw [hH, Nat.mul_assoc 6 m l]
  show 6 * m * l * d + H ≤ 4 * d * d + 2 * H * H + H * l
  rw [e6]
  exact key

/-- One order-three cell for every multiplicity: for every `m ≥ 3` the cell `(3m − 3, 3)` satisfies the counting
bound and the parity condition and admits no `m`-fold Langford sequence. -/
theorem not_order_three_internal (m : ℕ) (hm : 3 ≤ m) :
    2 * (3 * m - 3) + 3 ≤ 2 * m * 3 + 1 ∧ (m % 2 = 1 → 3 * (2 * (3 * m - 3) + 3 + 1) % 4 = 0) ∧
      ¬ ∃ s : ℕ → ℕ, Langford.IsLangford m (3 * m - 3) 3 s := by
  refine ⟨by omega, fun hodd => by omega, ?_⟩
  rintro ⟨s, hs⟩
  rcases Nat.lt_or_ge m 4 with h | h
  · -- `m = 3`: the cell `(6, 3)`
    obtain rfl : m = 3 := by omega
    have e : 3 * 3 - 3 = 6 := by norm_num
    rw [e] at hs
    exact not_threeFold_six_three_internal ⟨s, hs⟩
  · -- `m ≥ 4`: with `m = n + 1` the forced-endpoint bound reads `12n ≤ 24`
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have e : 3 * (n + 1) - 3 = 3 * n := by omega
    rw [e] at hs
    have hb := forced_endpoint_internal (n + 1) (3 * n) 3 (by omega) (by omega) (by norm_num) s hs
    linarith

/-- The top of the order-two row is empty for every `m ≥ 3`: no `m`-fold Langford sequence of order `2` and defect
`2m − 1` exists. For even `m` the cell satisfies the counting bound and the parity condition; for odd `m` the parity
condition already excludes it. -/
theorem not_order_two_top_internal (m : ℕ) (hm : 3 ≤ m) :
    ¬ ∃ s : ℕ → ℕ, Langford.IsLangford m (2 * m - 1) 2 s := by
  rintro ⟨s, hs⟩
  -- with `m = n + 1` the forced-endpoint bound reads `2n ≤ 2`
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have e : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [e] at hs
  have hb := forced_endpoint_internal (n + 1) (2 * n + 1) 2 (by omega) (by omega) (by norm_num) s hs
  linarith

end L2
