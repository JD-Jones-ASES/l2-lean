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
  induction L using Finset.induction_on_max with
  | empty =>
    obtain ⟨x, hx0, _⟩ := hx
    exact absurd hx0 (Finset.notMem_empty x)
  | insert a s hlt _ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hs : ∀ x ∈ s, 1 ≤ x := fun x hx => hL x (Finset.mem_insert_of_mem hx)
    have hbot := Nec.bottom_le_sum s hs
    obtain ⟨x, hxL, hxc⟩ := hx
    rw [Finset.card_insert_of_notMem ha] at hxc
    -- the witness lies at or below the maximum `a`, so `a` exceeds the new cardinality
    have hxa : x ≤ a := by
      rcases Finset.mem_insert.1 hxL with h | h
      · exact h.le
      · exact (hlt x h).le
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    nlinarith

/-- A finite set of `k` positive integers with the sum of `[1, k]` is `[1, k]`. -/
theorem bottom_eq (L : Finset ℕ) (hL : ∀ x ∈ L, 1 ≤ x) (hsum : 2 * ∑ x ∈ L, x = L.card * (L.card + 1)) :
    L = Finset.Icc 1 L.card := by
  have hsub : L ⊆ Finset.Icc 1 L.card := by
    intro x hx
    rw [Finset.mem_Icc]
    refine ⟨hL x hx, ?_⟩
    by_contra hc
    have hlt := bottom_lt_sum L hL ⟨x, hx, not_le.mp hc⟩
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Nat.card_Icc]; omega)

end Str

/-- Equality in the counting bound is rigid: `2d + l = 2ml + 1` if and only if every pair straddles the midpoint:
every position `i ≤ ml` has `ml < i + s i`. -/
theorem tight_iff_straddle_internal (m d l : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (s : ℕ → ℕ)
    (hs : Langford.IsLangford m d l s) :
    2 * d + l = 2 * m * l + 1 ↔ ∀ i : ℕ, 1 ≤ i → i ≤ m * l → m * l < i + s i := by
  obtain ⟨A, hA⟩ := Nec.exists_choice hs
  set L := Nec.leftEnds d l A with hLdef
  set R := Nec.rightEnds d l A with hRdef
  have hdisj : Disjoint L R := Nec.left_right_disjoint hd hl hs hA
  have hunion : L ∪ R = Finset.Icc 1 (2 * m * l) := Nec.left_right_union hd hl hs hA
  have hcL : L.card = m * l := Nec.card_left hd hl hs hA
  have hcR : R.card = m * l := Nec.card_right hd hl hs hA
  have hsum : ∑ x ∈ R, x = ∑ x ∈ L, x + m * ∑ p ∈ Finset.Icc d (d + l - 1), p :=
    Nec.sum_right_sub_left hd hl hs hA
  have hgap := Nec.sum_Icc_d d l
  -- name the quantities
  set H := m * l with hH
  have hH1 : 1 ≤ H := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h2ml : 2 * m * l = 2 * H := by rw [hH]; ring
  set X := 2 * d + l - 1 with hX
  have hLmem : ∀ x ∈ L, 1 ≤ x := by
    intro x hx
    have : x ∈ L ∪ R := Finset.mem_union_left _ hx
    rw [hunion, Finset.mem_Icc] at this
    exact this.1
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
  constructor
  · -- equality forces the left ends to be `[1, H]`, and every pair then straddles `H`
    intro htight
    have hXH : X = 2 * H := by omega
    rw [hXH] at hdist
    have h2SL : 2 * SL = H * (H + 1) := by linarith
    have hLeq : L = Finset.Icc 1 H := by
      have h := Str.bottom_eq L hLmem (by rw [hcL]; exact h2SL)
      rwa [hcL] at h
    intro i hi1 hiH
    have hiL : i ∈ L := by
      rw [hLeq, Finset.mem_Icc]
      exact ⟨hi1, hiH⟩
    obtain ⟨p, hp, hip⟩ := Finset.mem_biUnion.1 hiL
    have hp' := Nec.mem_window hl hp
    have hv := Nec.value_left hA hp'.1 hp'.2 hip
    have hR : i + p ∈ R := Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2 ⟨i, hip, rfl⟩⟩
    have hnotL : i + p ∉ L := fun h => Finset.disjoint_left.1 hdisj h hR
    rw [hv.2.2]
    by_contra hc
    apply hnotL
    rw [hLeq, Finset.mem_Icc]
    constructor <;> omega
  · -- if every pair straddles `H`, the right ends are `[H + 1, 2H]`, and the distance sum is `H²`
    intro hstr
    have hRgt : ∀ x ∈ R, H < x := by
      intro x hx
      obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.1 hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hxp
      have hp' := Nec.mem_window hl hp
      have hv := Nec.value_left hA hp'.1 hp'.2 ha
      by_contra hc
      have h1 := hstr a hv.1 (by omega)
      rw [hv.2.2] at h1
      exact hc h1
    have hRsub : R ⊆ Finset.Icc (H + 1) (2 * H) := by
      intro x hx
      have hxU : x ∈ L ∪ R := Finset.mem_union_right _ hx
      rw [hunion, Finset.mem_Icc, h2ml] at hxU
      have h1 := hRgt x hx
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hReq : R = Finset.Icc (H + 1) (2 * H) :=
      Finset.eq_of_subset_of_card_le hRsub (by rw [Nat.card_Icc, hcR]; omega)
    have hSR : 2 * SR = H * (3 * H + 1) := by
      have h := Nec.sum_Icc_d (H + 1) H
      have e1 : H + 1 + H - 1 = 2 * H := by omega
      have e2 : 2 * (H + 1) + H - 1 = 3 * H + 1 := by omega
      rw [e1, e2, ← hReq] at h
      exact h
    have h2SL : 2 * SL = H * (H + 1) := by linarith
    have hHX : H * X = H * (2 * H) := by linarith
    have hX2 : X = 2 * H := Nat.eq_of_mul_eq_mul_left (by omega) hHX
    omega

end L2
