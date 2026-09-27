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
  induction N generalizing R with
  | zero =>
    have : R = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      have := hR x hx
      omega
    subst this
    simp
  | succ N ih =>
    by_cases hN : N + 1 ∈ R
    · -- remove the top element `N + 1`
      set R' := R.erase (N + 1) with hR'
      have hsub : ∀ x ∈ R', 1 ≤ x ∧ x ≤ N := by
        intro x hx
        rw [Finset.mem_erase] at hx
        have := hR x hx.2
        omega
      have hcard : R.card = R'.card + 1 := (Finset.card_erase_add_one hN).symm
      have hsum : ∑ x ∈ R, x = ∑ x ∈ R', x + (N + 1) := by
        rw [hR', Finset.sum_erase_add _ _ hN]
      have hk : R'.card ≤ N := by
        have h1 : R' ⊆ Finset.Icc 1 N := by
          intro x hx
          rw [Finset.mem_Icc]
          exact hsub x hx
        have := Finset.card_le_card h1
        simpa using this
      have ih' := ih R' hsub
      rw [hcard, hsum]
      obtain ⟨t, ht⟩ : ∃ t, N = R'.card + t := ⟨N - R'.card, by omega⟩
      have e1 : 2 * N + 1 - R'.card = R'.card + 2 * t + 1 := by omega
      have e2 : 2 * (N + 1) + 1 - (R'.card + 1) = R'.card + 2 * t + 2 := by omega
      rw [e1] at ih'
      rw [e2]
      have e3 : (R'.card + 1) * (R'.card + 2 * t + 2) =
          R'.card * (R'.card + 2 * t + 1) + 2 * (N + 1) := by
        rw [ht]; ring
      omega
    · have hsub : ∀ x ∈ R, 1 ≤ x ∧ x ≤ N := by
        intro x hx
        have := hR x hx
        have : x ≠ N + 1 := fun h => hN (h ▸ hx)
        omega
      have ih' := ih R hsub
      calc 2 * ∑ x ∈ R, x ≤ R.card * (2 * N + 1 - R.card) := ih'
        _ ≤ R.card * (2 * (N + 1) + 1 - R.card) := Nat.mul_le_mul_left _ (by omega)

/-- A `k`-subset of the positive integers has sum at least that of `[1, k]`: `2·ΣL ≥ k(k + 1)`. -/
theorem bottom_le_sum (L : Finset ℕ) (hL : ∀ x ∈ L, 1 ≤ x) :
    L.card * (L.card + 1) ≤ 2 * ∑ x ∈ L, x := by
  induction L using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hs : ∀ x ∈ s, 1 ≤ x := fun x hx => hL x (Finset.mem_insert_of_mem hx)
    have ha1 : 1 ≤ a := hL a (Finset.mem_insert_self a s)
    have hk : s.card ≤ a - 1 := by
      have h1 : s ⊆ Finset.Ico 1 a := by
        intro x hx
        rw [Finset.mem_Ico]
        exact ⟨hs x hx, hlt x hx⟩
      have := Finset.card_le_card h1
      simpa using this
    have ih' := ih hs
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    have hk' : s.card + 1 ≤ a := by omega
    nlinarith

/-- The sum of the differences: `2 · Σ_{p=d}^{d+l−1} p = l(2d + l − 1)`. -/
theorem sum_Icc_d (d l : ℕ) :
    2 * ∑ p ∈ Finset.Icc d (d + l - 1), p = l * (2 * d + l - 1) := by
  have key : ∀ k : ℕ, 2 * ∑ p ∈ Finset.Icc d (d + k), p = (k + 1) * (2 * d + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      ring
  rcases Nat.eq_zero_or_pos l with h | h
  · subst h
    simp only [zero_mul, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_Icc] at hx
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    have e1 : d + (k + 1) - 1 = d + k := by omega
    have e2 : 2 * d + (k + 1) - 1 = 2 * d + k := by omega
    rw [e1, e2]
    exact key k

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
  have h : ∀ p : ℕ, ∃ B : Finset ℕ, d ≤ p → p < d + l →
      B.card = m ∧
        (∀ a ∈ B, 1 ≤ a ∧ a + p ≤ 2 * m * l ∧ a + p ∉ B) ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ 2 * m * l → (s i = p ↔ i ∈ B ∨ ∃ a ∈ B, i = a + p) := by
    intro p
    by_cases hp : d ≤ p ∧ p < d + l
    · obtain ⟨B, hB⟩ := hs.2 p hp.1 hp.2
      exact ⟨B, fun _ _ => hB⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ hp⟩
  choose A hA using h
  exact ⟨A, hA⟩

/-- The left ends of all pairs. -/
def leftEnds (d l : ℕ) (A : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.Icc d (d + l - 1)).biUnion A

/-- The right ends of all pairs. -/
def rightEnds (d l : ℕ) (A : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.Icc d (d + l - 1)).biUnion fun p => (A p).image (· + p)

/-- A difference of the window `[d, d + l − 1]` satisfies the bounds of `Choice`. -/
theorem mem_window {d l p : ℕ} (hl : 1 ≤ l) (hp : p ∈ Finset.Icc d (d + l - 1)) :
    d ≤ p ∧ p < d + l := by
  rw [Finset.mem_Icc] at hp
  omega

/-- A left end of a pair of difference `p` is a position carrying the value `p`. -/
theorem value_left {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hA : Choice m d l s A) {p a : ℕ}
    (h1 : d ≤ p) (h2 : p < d + l) (ha : a ∈ A p) :
    1 ≤ a ∧ a ≤ 2 * m * l ∧ s a = p := by
  obtain ⟨_, hB, hC⟩ := hA p h1 h2
  obtain ⟨ha1, ha2, _⟩ := hB a ha
  exact ⟨ha1, by omega, (hC a ha1 (by omega)).2 (Or.inl ha)⟩

/-- A right end of a pair of difference `p` is a position carrying the value `p`. -/
theorem value_right {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hA : Choice m d l s A) {p a : ℕ}
    (h1 : d ≤ p) (h2 : p < d + l) (ha : a ∈ A p) :
    1 ≤ a + p ∧ a + p ≤ 2 * m * l ∧ s (a + p) = p := by
  obtain ⟨_, hB, hC⟩ := hA p h1 h2
  obtain ⟨ha1, ha2, _⟩ := hB a ha
  exact ⟨by omega, ha2, (hC (a + p) (by omega) ha2).2 (Or.inr ⟨a, ha, rfl⟩)⟩

/-- The left-end sets of distinct differences are disjoint (a position carries one value). -/
theorem pairwise_left {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hl : 1 ≤ l)
    (hA : Choice m d l s A) :
    ((Finset.Icc d (d + l - 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint A := by
  intro p hp q hq hpq
  have hp' := mem_window hl (Finset.mem_coe.1 hp)
  have hq' := mem_window hl (Finset.mem_coe.1 hq)
  refine Finset.disjoint_left.2 fun x hxp hxq => hpq ?_
  have e1 := (value_left hA hp'.1 hp'.2 hxp).2.2
  have e2 := (value_left hA hq'.1 hq'.2 hxq).2.2
  exact e1.symm.trans e2

/-- The right-end sets of distinct differences are disjoint (a position carries one value). -/
theorem pairwise_right {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hl : 1 ≤ l)
    (hA : Choice m d l s A) :
    ((Finset.Icc d (d + l - 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun p => (A p).image (· + p) := by
  intro p hp q hq hpq
  have hp' := mem_window hl (Finset.mem_coe.1 hp)
  have hq' := mem_window hl (Finset.mem_coe.1 hq)
  refine Finset.disjoint_left.2 fun x hxp hxq => hpq ?_
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hxp
  obtain ⟨b, hb, hbx⟩ := Finset.mem_image.1 hxq
  have e1 := (value_right hA hp'.1 hp'.2 ha).2.2
  have e2 := (value_right hA hq'.1 hq'.2 hb).2.2
  rw [hbx] at e2
  exact e1.symm.trans e2

set_option linter.unusedVariables false in
/-- No position is both a left end and a right end. -/
theorem left_right_disjoint {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hd : 1 ≤ d) (hl : 1 ≤ l)
    (hs : Langford.IsLangford m d l s) (hA : Choice m d l s A) :
    Disjoint (leftEnds d l A) (rightEnds d l A) := by
  refine Finset.disjoint_left.2 fun x hxL hxR => ?_
  obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.1 hxL
  obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.1 hxR
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hxq
  have hp' := mem_window hl hp
  have hq' := mem_window hl hq
  have e1 := (value_left hA hp'.1 hp'.2 hxp).2.2
  have e2 := (value_right hA hq'.1 hq'.2 ha).2.2
  have hpq : p = q := e1.symm.trans e2
  subst hpq
  exact ((hA p hp'.1 hp'.2).2.1 a ha).2.2 hxp

set_option linter.unusedVariables false in
/-- The left ends and the right ends together are the positions `[1, 2ml]`. -/
theorem left_right_union {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hd : 1 ≤ d) (hl : 1 ≤ l)
    (hs : Langford.IsLangford m d l s) (hA : Choice m d l s A) :
    leftEnds d l A ∪ rightEnds d l A = Finset.Icc 1 (2 * m * l) := by
  ext x
  rw [Finset.mem_union, Finset.mem_Icc]
  constructor
  · rintro (hxL | hxR)
    · obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.1 hxL
      have hp' := mem_window hl hp
      have := value_left hA hp'.1 hp'.2 hxp
      exact ⟨this.1, this.2.1⟩
    · obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.1 hxR
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hxq
      have hq' := mem_window hl hq
      have := value_right hA hq'.1 hq'.2 ha
      exact ⟨this.1, this.2.1⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨hv1, hv2⟩ := hs.1 x h1 h2
    have hp : s x ∈ Finset.Icc d (d + l - 1) := by
      rw [Finset.mem_Icc]
      omega
    rcases ((hA (s x) hv1 hv2).2.2 x h1 h2).1 rfl with hx | ⟨a, ha, hax⟩
    · exact Or.inl (Finset.mem_biUnion.2 ⟨s x, hp, hx⟩)
    · exact Or.inr (Finset.mem_biUnion.2 ⟨s x, hp, Finset.mem_image.2 ⟨a, ha, hax.symm⟩⟩)

set_option linter.unusedVariables false in
/-- There are `ml` left ends. -/
theorem card_left {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hd : 1 ≤ d) (hl : 1 ≤ l)
    (hs : Langford.IsLangford m d l s) (hA : Choice m d l s A) :
    (leftEnds d l A).card = m * l := by
  unfold leftEnds
  rw [Finset.card_biUnion (pairwise_left hl hA)]
  rw [Finset.sum_congr rfl fun p hp =>
    (hA p (mem_window hl hp).1 (mem_window hl hp).2).1]
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
  have : d + l - 1 + 1 - d = l := by omega
  rw [this, Nat.mul_comm]

set_option linter.unusedVariables false in
/-- There are `ml` right ends. -/
theorem card_right {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hd : 1 ≤ d) (hl : 1 ≤ l)
    (hs : Langford.IsLangford m d l s) (hA : Choice m d l s A) :
    (rightEnds d l A).card = m * l := by
  unfold rightEnds
  rw [Finset.card_biUnion (pairwise_right hl hA)]
  rw [Finset.sum_congr rfl fun p _ => Finset.card_image_of_injective _ (add_left_injective p)]
  rw [Finset.sum_congr rfl fun p hp =>
    (hA p (mem_window hl hp).1 (mem_window hl hp).2).1]
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
  have : d + l - 1 + 1 - d = l := by omega
  rw [this, Nat.mul_comm]

set_option linter.unusedVariables false in
/-- The distance sum: `ΣR = ΣL + m · Σ_{p=d}^{d+l−1} p`. -/
theorem sum_right_sub_left {m d l : ℕ} {s : ℕ → ℕ} {A : ℕ → Finset ℕ} (hd : 1 ≤ d) (hl : 1 ≤ l)
    (hs : Langford.IsLangford m d l s) (hA : Choice m d l s A) :
    ∑ x ∈ rightEnds d l A, x =
      ∑ x ∈ leftEnds d l A, x + m * ∑ p ∈ Finset.Icc d (d + l - 1), p := by
  unfold leftEnds rightEnds
  rw [Finset.sum_biUnion (pairwise_right hl hA), Finset.sum_biUnion (pairwise_left hl hA),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_image (fun a _ b _ h => add_right_cancel h), Finset.sum_add_distrib,
    Finset.sum_const, (hA p (mem_window hl hp).1 (mem_window hl hp).2).1, smul_eq_mul]

end Nec

/-- Every `m`-fold Langford sequence (`m, d, l ≥ 1`) satisfies `(2m − 1)l ≥ 2d − 1`, and for odd `m`
also `l(2d + l + 1) ≡ 0 (mod 4)`. -/
theorem necessary_internal (m d l : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (hl : 1 ≤ l) (s : ℕ → ℕ)
    (hs : Langford.IsLangford m d l s) :
    2 * d + l ≤ 2 * m * l + 1 ∧ (m % 2 = 1 → l * (2 * d + l + 1) % 4 = 0) := by
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
  -- the top bound on the right ends and the bottom bound on the left ends
  have hRmem : ∀ x ∈ R, 1 ≤ x ∧ x ≤ 2 * H := by
    intro x hx
    have : x ∈ L ∪ R := Finset.mem_union_right _ hx
    rw [hunion, Finset.mem_Icc, h2ml] at this
    exact this
  have htop := Nec.sum_le_top R (2 * H) hRmem
  rw [hcR] at htop
  have e3 : 2 * (2 * H) + 1 - H = 3 * H + 1 := by omega
  rw [e3] at htop
  have hLmem : ∀ x ∈ L, 1 ≤ x := by
    intro x hx
    have : x ∈ L ∪ R := Finset.mem_union_left _ hx
    rw [hunion, Finset.mem_Icc] at this
    exact this.1
  have hbot := Nec.bottom_le_sum L hLmem
  rw [hcL] at hbot
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
  · -- the distance bound
    have hle : H * X ≤ H * (2 * H) := by nlinarith
    have := Nat.le_of_mul_le_mul_left hle (by omega)
    omega
  · -- the parity
    intro hodd
    have h4 : H * X + 2 * H * (2 * H + 1) = 4 * SR := by linarith
    have hY : 2 * d + l + 1 = X + 2 := by omega
    have e6 : H * X + 2 * H * (2 * H + 1) = m * (l * (2 * d + l + 1)) + 4 * (H * H) := by
      rw [hY, hH]
      ring
    have hdvd : 4 ∣ m * (l * (2 * d + l + 1)) := by
      have : 4 ∣ m * (l * (2 * d + l + 1)) + 4 * (H * H) := by
        rw [← e6, h4]
        exact Dvd.intro SR rfl
      exact (Nat.dvd_add_left (Dvd.intro _ rfl)).1 this
    have hcop : Nat.Coprime 4 m := by
      have : Nat.Coprime 2 m := Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd)
      simpa using this.pow_left 2
    exact Nat.mod_eq_zero_of_dvd (hcop.dvd_of_dvd_mul_left hdvd)

end L2
