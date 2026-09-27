import L2.Necessity

/-!
# The cell `(6, 3)` of the three-fold sequences

A three-fold Langford sequence of order `3` and defect `6` would occupy the positions `1, …, 18`
with three pairs of each difference `6`, `7`, `8`. Positions `1, …, 6` must be left ends and
`13, …, 18` right ends; the distance sum forces the three remaining left ends among `7, …, 12` to
sum to `33`, hence to be `10, 11, 12`, which are then the left ends of three pairs of difference
`6`. But position `7` is a right end, and its partner in `[1, 6]` forces a fourth pair of
difference `6`.
-/

namespace L2

/-- The only three-element subset of `[7, 12]` with sum `33` is `{10, 11, 12}`: the finite check
behind the distance-sum step of the cell `(6, 3)`. -/
theorem three_subset_sum_33 :
    ∀ U ∈ (Finset.Icc 7 12).powerset, U.card = 3 → ∑ x ∈ U, x = 33 → U = {10, 11, 12} := by
  decide

/-- No three-fold Langford sequence of order `3` and defect `6` exists. -/
theorem not_threeFold_six_three_internal : ¬ ∃ s : ℕ → ℕ, Langford.IsLangford 3 6 3 s := by
  rintro ⟨s, hs⟩
  obtain ⟨A, hA⟩ := Nec.exists_choice hs
  have hdis := Nec.left_right_disjoint (by norm_num) (by norm_num) hs hA
  have huni := Nec.left_right_union (by norm_num) (by norm_num) hs hA
  have hcL := Nec.card_left (by norm_num) (by norm_num) hs hA
  have hsum := Nec.sum_right_sub_left (by norm_num) (by norm_num) hs hA
  -- The clauses of the choice at each difference `p ∈ [6, 8]`.
  have hcard : ∀ p, 6 ≤ p → p ≤ 8 → (A p).card = 3 := fun p h1 _ => (hA p h1 (by omega)).1
  have hbd : ∀ p, 6 ≤ p → p ≤ 8 → ∀ a ∈ A p, 1 ≤ a ∧ a + p ≤ 18 := by
    intro p h1 _ a ha
    have h := (hA p h1 (by omega)).2.1 a ha
    exact ⟨h.1, by omega⟩
  have hval : ∀ p, 6 ≤ p → p ≤ 8 → ∀ a ∈ A p, ∀ x, x = a + p → s x = p := by
    intro p h1 h2 a ha x hx
    obtain ⟨ha1, ha2⟩ := hbd p h1 h2 a ha
    exact ((hA p h1 (by omega)).2.2 x (by omega) (by omega)).mpr (Or.inr ⟨a, ha, hx⟩)
  have memL : ∀ x, x ∈ Nec.leftEnds 6 3 A ↔ ∃ p, 6 ≤ p ∧ p ≤ 8 ∧ x ∈ A p := by
    intro x
    simp only [Nec.leftEnds, Finset.mem_biUnion, Finset.mem_Icc]
    constructor
    · rintro ⟨p, ⟨h1, h2⟩, h⟩
      exact ⟨p, h1, by omega, h⟩
    · rintro ⟨p, h1, h2, h⟩
      exact ⟨p, ⟨h1, by omega⟩, h⟩
  have memR : ∀ x, x ∈ Nec.rightEnds 6 3 A ↔ ∃ p, 6 ≤ p ∧ p ≤ 8 ∧ ∃ a ∈ A p, a + p = x := by
    intro x
    simp only [Nec.rightEnds, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨p, ⟨h1, h2⟩, h⟩
      exact ⟨p, h1, by omega, h⟩
    · rintro ⟨p, h1, h2, h⟩
      exact ⟨p, ⟨h1, by omega⟩, h⟩
  set L := Nec.leftEnds 6 3 A with hLdef
  set R := Nec.rightEnds 6 3 A with hRdef
  have hLR : ∀ x, 1 ≤ x → x ≤ 18 → x ∈ L ∨ x ∈ R := by
    intro x h1 h2
    have hx : x ∈ L ∪ R := by
      rw [huni]
      exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
    exact Finset.mem_union.mp hx
  -- Left ends lie in `[1, 12]`; positions `1, …, 6` are left ends.
  have hL1 : ∀ x ∈ L, 1 ≤ x ∧ x ≤ 12 := by
    intro x hx
    obtain ⟨p, h1, h2, hp⟩ := (memL x).mp hx
    have := hbd p h1 h2 x hp
    omega
  have h16 : ∀ x, 1 ≤ x → x ≤ 6 → x ∈ L := by
    intro x h1 h2
    rcases hLR x h1 (by omega) with h | h
    · exact h
    · obtain ⟨p, hp1, hp2, a, ha, hax⟩ := (memR x).mp h
      have := hbd p hp1 hp2 a ha
      omega
  -- The distance sum: `ΣL + ΣR = 171` and `ΣR = ΣL + 63`, so `ΣL = 54`.
  have htot : ∑ x ∈ L, x + ∑ x ∈ R, x = 171 := by
    have h := Finset.sum_union hdis (f := fun x => x)
    rw [huni] at h
    have h171 : ∑ x ∈ Finset.Icc 1 (2 * 3 * 3), x = 171 := by decide
    omega
  have h21 : ∑ p ∈ Finset.Icc 6 (6 + 3 - 1), p = 21 := by decide
  rw [h21] at hsum
  have hsL : ∑ x ∈ L, x = 54 := by omega
  -- The left ends above `6`: three of them, with sum `33`.
  set T := L.filter (fun x => 7 ≤ x) with hT
  have hsplit : L = Finset.Icc 1 6 ∪ T := by
    ext x
    simp only [hT, Finset.mem_union, Finset.mem_Icc, Finset.mem_filter]
    constructor
    · intro hx
      have := hL1 x hx
      by_cases h : 7 ≤ x
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl ⟨this.1, by omega⟩
    · rintro (⟨h1, h2⟩ | ⟨hx, -⟩)
      · exact h16 x h1 h2
      · exact hx
  have hdisT : Disjoint (Finset.Icc 1 6) T := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    simp only [hT, Finset.mem_filter, Finset.mem_Icc] at hx hxT
    omega
  have hcT : T.card = 3 := by
    have h := Finset.card_union_of_disjoint hdisT
    rw [← hsplit, hcL] at h
    have h6 : (Finset.Icc 1 6).card = 6 := by decide
    omega
  have hsT : ∑ x ∈ T, x = 33 := by
    have h := Finset.sum_union hdisT (f := fun x => x)
    rw [← hsplit, hsL] at h
    have h6 : ∑ x ∈ Finset.Icc 1 6, x = 21 := by decide
    omega
  have hTsub : T ⊆ Finset.Icc 7 12 := by
    intro x hx
    simp only [hT, Finset.mem_filter] at hx
    have := hL1 x hx.1
    exact Finset.mem_Icc.mpr ⟨hx.2, this.2⟩
  have hTeq : T = {10, 11, 12} :=
    three_subset_sum_33 T (Finset.mem_powerset.mpr hTsub) hcT hsT
  have hTL : ∀ x ∈ T, x ∈ L := fun x hx => (Finset.mem_filter.mp hx).1
  have h10 : 10 ∈ L := hTL 10 (by rw [hTeq]; simp)
  have h11 : 11 ∈ L := hTL 11 (by rw [hTeq]; simp)
  have h12 : 12 ∈ L := hTL 12 (by rw [hTeq]; simp)
  have h7 : 7 ∉ L := by
    intro h
    have h7T : 7 ∈ T := Finset.mem_filter.mpr ⟨h, le_rfl⟩
    rw [hTeq] at h7T
    simp at h7T
  -- The partner chase: `12`, `11`, `10` are left ends of pairs of difference `6`.
  obtain ⟨p12, h121, h122, h12A⟩ := (memL 12).mp h12
  have := hbd p12 h121 h122 12 h12A
  obtain rfl : p12 = 6 := by omega
  have s18 := hval 6 le_rfl (by norm_num) 12 h12A 18 rfl
  obtain ⟨p11, h111, h112, h11A⟩ := (memL 11).mp h11
  have := hbd p11 h111 h112 11 h11A
  have hp11 : p11 = 6 := by
    rcases (by omega : p11 = 6 ∨ p11 = 7) with h | h
    · exact h
    · subst h
      have := hval 7 (by norm_num) (by norm_num) 11 h11A 18 rfl
      omega
  subst hp11
  have s17 := hval 6 le_rfl (by norm_num) 11 h11A 17 rfl
  obtain ⟨p10, h101, h102, h10A⟩ := (memL 10).mp h10
  have hp10 : p10 = 6 := by
    rcases (by omega : p10 = 6 ∨ p10 = 7 ∨ p10 = 8) with h | h | h
    · exact h
    · subst h
      have := hval 7 (by norm_num) (by norm_num) 10 h10A 17 rfl
      omega
    · subst h
      have := hval 8 (by norm_num) le_rfl 10 h10A 18 rfl
      omega
  subst hp10
  -- Position `7` is a right end; its partner is `1`, a fourth left end of difference `6`.
  have h7R : 7 ∈ R := (hLR 7 (by norm_num) (by norm_num)).resolve_left h7
  obtain ⟨p7, hp71, hp72, a7, ha7, he7⟩ := (memR 7).mp h7R
  have := hbd p7 hp71 hp72 a7 ha7
  obtain rfl : p7 = 6 := by omega
  obtain rfl : a7 = 1 := by omega
  have hsub : ({1, 10, 11, 12} : Finset ℕ) ⊆ A 6 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h4 := Finset.card_le_card hsub
  rw [hcard 6 le_rfl (by norm_num)] at h4
  have : ({1, 10, 11, 12} : Finset ℕ).card = 4 := by decide
  omega

end L2
