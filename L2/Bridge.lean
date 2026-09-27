import L2.Multi
import L2.Defs

/-!
# From a certificate to a sequence

An `m`-colour certificate has at most `ml` pairs and covers the `2ml` positions of `[1, 2ml]`, so
it has exactly `ml` pairs and every position is the end of exactly one pair. Each colour has at
least `l` pairs (its `l` differences are distinct), hence exactly `l`; the colours are pairwise
disjoint; and each colour has one pair of each difference, so every difference `p` in
`[d, d + l − 1]` is carried by exactly `m` pairs. Reading at each position the difference of the pair
that contains it gives an `m`-fold Langford sequence in the sense of `Langford.IsLangford`.
-/

namespace L2
noncomputable section

/-- The union of the colours. -/
def allPairs (m : ℕ) (C : ℕ → Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) := (Finset.range m).biUnion C

/-- A certificate has exactly `ml` pairs: its `2ml` positions need at least `ml` pairs, and it has
at most `ml`. -/
theorem MultiPairing.card_allPairs {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)}
    (h : MultiPairing m d l C) : (allPairs m C).card = m * l.toNat := by
  obtain ⟨L, rfl⟩ : ∃ L : ℕ, l = L := ⟨l.toNat, by have := h.order_pos; omega⟩
  have hc := h.card_le
  simp only [Int.toNat_natCast] at hc ⊢
  have hE : pairEndpoints (allPairs m C) = Finset.Icc 1 (2 * m * (L : ℤ)) := h.endpoints
  have h1 := card_pairEndpoints_le (allPairs m C)
  rw [hE, Int.card_Icc] at h1
  have h2 : (allPairs m C).card ≤ m * L := Finset.card_biUnion_le.trans hc
  have h3 : (2 * (m : ℤ) * L + 1 - 1).toNat = 2 * (m * L) := by
    rw [show (2 * (m : ℤ) * L + 1 - 1) = ((2 * (m * L) : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  omega

/-- Every position of `[1, 2ml]` is exactly one oriented end of one pair. -/
theorem MultiPairing.endpoint_bijOn {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)}
    (h : MultiPairing m d l C) :
    Set.BijOn orientedEndpoint (orientedPairs (allPairs m C)) (Finset.Icc 1 (2 * m * l)) := by
  apply (Finset.image_eq_iff_bijOn_of_card ?_).mp
  · exact (orientedEndpoint_image _).trans h.endpoints
  · obtain ⟨L, rfl⟩ : ∃ L : ℕ, l = L := ⟨l.toNat, by have := h.order_pos; omega⟩
    rw [card_orientedPairs, h.card_allPairs, Int.card_Icc, Int.toNat_natCast]
    rw [show (2 * (m : ℤ) * L + 1 - 1) = ((2 * (m * L) : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]

/-- Every colour has at least `l` pairs: its differences are the `l` values of `[d, d + l − 1]`. -/
theorem MultiPairing.toNat_le_card_colour {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {c : ℕ}
    (h : MultiPairing m d l C) (hc : c < m) : l.toNat ≤ (C c).card := by
  have h1 : (pairDifferences (C c)).card ≤ (C c).card := Finset.card_image_le
  rw [h.differences c hc, Int.card_Icc] at h1
  have : d + l - 1 + 1 - d = l := by ring
  rwa [this] at h1

/-- Every colour has exactly `l` pairs. -/
theorem MultiPairing.card_colour {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {c : ℕ}
    (h : MultiPairing m d l C) (hc : c < m) : (C c).card = l.toNat := by
  apply le_antisymm _ (h.toNat_le_card_colour hc)
  have hmem : c ∈ Finset.range m := Finset.mem_range.mpr hc
  have hs := Finset.add_sum_erase (Finset.range m) (fun c => (C c).card) hmem
  have hlow : ((Finset.range m).erase c).card • l.toNat ≤
      ∑ x ∈ (Finset.range m).erase c, (C x).card :=
    Finset.card_nsmul_le_sum _ _ _ (fun x hx =>
      h.toNat_le_card_colour (Finset.mem_range.mp (Finset.mem_of_mem_erase hx)))
  rw [Finset.card_erase_of_mem hmem, Finset.card_range, smul_eq_mul] at hlow
  have hc2 := h.card_le
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlow
  rw [add_mul, one_mul] at hc2
  omega

/-- Distinct colours share no pair: the other colours hold at most `(m − 1)l` pairs, and together
with the `l` pairs of one colour they make up all `ml` pairs, so nothing is counted twice. -/
theorem MultiPairing.pairwise_disjoint {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {c c' : ℕ}
    (h : MultiPairing m d l C) (hc : c < m) (hc' : c' < m) (hne : c ≠ c') :
    Disjoint (C c) (C c') := by
  have hmem' : c' ∈ Finset.range m := Finset.mem_range.mpr hc'
  have hU : allPairs m C = C c' ∪ ((Finset.range m).erase c').biUnion C := by
    unfold allPairs
    conv_lhs => rw [← Finset.insert_erase hmem']
    rw [Finset.biUnion_insert]
  have hR : (((Finset.range m).erase c').biUnion C).card ≤ (m - 1) * l.toNat := by
    refine Finset.card_biUnion_le.trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl (fun x hx =>
        h.card_colour (Finset.mem_range.mp (Finset.mem_of_mem_erase hx))),
      Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hmem', Finset.card_range]
  have hI := Finset.card_union_add_card_inter (C c') (((Finset.range m).erase c').biUnion C)
  rw [← hU, h.card_allPairs, h.card_colour hc'] at hI
  have hempty : (C c' ∩ ((Finset.range m).erase c').biUnion C).card = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hR
    rw [add_mul, one_mul] at hI
    omega
  rw [Finset.card_eq_zero] at hempty
  rw [Finset.disjoint_left]
  intro q hq hq'
  have hin : q ∈ C c' ∩ ((Finset.range m).erase c').biUnion C :=
    Finset.mem_inter.mpr ⟨hq', Finset.mem_biUnion.mpr
      ⟨c, Finset.mem_erase.mpr ⟨hne, Finset.mem_range.mpr hc⟩, hq⟩⟩
  rw [hempty] at hin
  exact Finset.notMem_empty _ hin

/-- Within a colour, distinct pairs have distinct differences: a colour has `l` pairs and `l`
differences. -/
theorem MultiPairing.diff_injOn {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {c : ℕ}
    (h : MultiPairing m d l C) (hc : c < m) :
    Set.InjOn (fun q : ℤ × ℤ => q.2 - q.1) (C c) := by
  have h1 : ((C c).image (fun q : ℤ × ℤ => q.2 - q.1)).card = (C c).card := by
    have : ((C c).image (fun q : ℤ × ℤ => q.2 - q.1)) = pairDifferences (C c) := rfl
    rw [this, h.differences c hc, Int.card_Icc, h.card_colour hc]
    congr 1
    ring
  exact Finset.card_image_iff.mp h1

/-- Exactly `m` pairs of the certificate have difference `p`, for every `p ∈ [d, d + l − 1]`: one in
each colour, and the colours are disjoint. -/
theorem MultiPairing.card_fiber {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {p : ℤ}
    (h : MultiPairing m d l C) (hp : d ≤ p) (hp' : p ≤ d + l - 1) :
    ((allPairs m C).filter (fun q => q.2 - q.1 = p)).card = m := by
  have hF : (allPairs m C).filter (fun q => q.2 - q.1 = p) =
      (Finset.range m).biUnion (fun c => (C c).filter (fun q => q.2 - q.1 = p)) :=
    Finset.filter_biUnion _ _ _
  rw [hF, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (g := fun _ => 1), Finset.sum_const, Finset.card_range, smul_eq_mul,
      mul_one]
    intro c hc
    have hc' := Finset.mem_range.mp hc
    rw [Finset.card_eq_one]
    have hpm : p ∈ pairDifferences (C c) := by
      rw [h.differences c hc']
      exact Finset.mem_Icc.mpr ⟨hp, hp'⟩
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hpm
    refine ⟨q, ?_⟩
    ext r
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hr, hrp⟩
      exact h.diff_injOn hc' hr hq (show r.2 - r.1 = q.2 - q.1 by rw [hrp]; exact hqp.symm)
    · rintro rfl
      exact ⟨hq, hqp⟩
  · intro x hx y hy hxy
    exact Finset.disjoint_filter_filter
      (h.pairwise_disjoint (Finset.mem_range.mp (Finset.mem_coe.mp hx))
        (Finset.mem_range.mp (Finset.mem_coe.mp hy)) hxy)

/-- Every pair of a certificate has its left end below its right end: its difference is at least
`d ≥ 1`. -/
theorem MultiPairing.left_lt_right {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {q : ℤ × ℤ}
    (h : MultiPairing m d l C) (hq : q ∈ allPairs m C) : q.1 < q.2 := by
  obtain ⟨c, hc, hqc⟩ := Finset.mem_biUnion.mp hq
  have hmem : q.2 - q.1 ∈ pairDifferences (C c) := Finset.mem_image.mpr ⟨q, hqc, rfl⟩
  rw [h.differences c (Finset.mem_range.mp hc)] at hmem
  have h1 := Finset.mem_Icc.mp hmem
  have h2 := h.defect_pos
  omega

/-- Every pair of a certificate has its difference in `[d, d + l − 1]`. -/
theorem MultiPairing.diff_mem {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {q : ℤ × ℤ}
    (h : MultiPairing m d l C) (hq : q ∈ allPairs m C) : d ≤ q.2 - q.1 ∧ q.2 - q.1 ≤ d + l - 1 := by
  obtain ⟨c, hc, hqc⟩ := Finset.mem_biUnion.mp hq
  have hmem : q.2 - q.1 ∈ pairDifferences (C c) := Finset.mem_image.mpr ⟨q, hqc, rfl⟩
  rw [h.differences c (Finset.mem_range.mp hc)] at hmem
  exact Finset.mem_Icc.mp hmem

/-- Both ends of every pair of a certificate lie in `[1, 2ml]`. -/
theorem MultiPairing.ends_mem {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {q : ℤ × ℤ}
    (h : MultiPairing m d l C) (hq : q ∈ allPairs m C) :
    (1 ≤ q.1 ∧ q.1 ≤ 2 * m * l) ∧ (1 ≤ q.2 ∧ q.2 ≤ 2 * m * l) := by
  have hE : pairEndpoints (allPairs m C) = Finset.Icc 1 (2 * m * l) := h.endpoints
  have h1 : q.1 ∈ pairEndpoints (allPairs m C) := Finset.mem_biUnion.mpr ⟨q, hq, by simp⟩
  have h2 : q.2 ∈ pairEndpoints (allPairs m C) := Finset.mem_biUnion.mpr ⟨q, hq, by simp⟩
  rw [hE, Finset.mem_Icc] at h1 h2
  exact ⟨h1, h2⟩

/-- The oriented end chosen at a position `x` belongs to the pair that has `x` as an end. -/
theorem MultiPairing.invFunOn_fst {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {q : ℤ × ℤ}
    {x : ℤ} (h : MultiPairing m d l C) (hq : q ∈ allPairs m C) (hx : q.1 = x ∨ q.2 = x) :
    (Function.invFunOn orientedEndpoint (orientedPairs (allPairs m C)) x).1 = q := by
  obtain ⟨b, hzb⟩ : ∃ b : Bool, orientedEndpoint (q, b) = x := by
    rcases hx with hx | hx
    · exact ⟨false, by simpa [orientedEndpoint] using hx⟩
    · exact ⟨true, by simpa [orientedEndpoint] using hx⟩
  have hz : (q, b) ∈ (orientedPairs (allPairs m C) : Set ((ℤ × ℤ) × Bool)) := by
    simp [orientedPairs, hq]
  have hex : ∃ z ∈ (orientedPairs (allPairs m C) : Set ((ℤ × ℤ) × Bool)),
      orientedEndpoint z = x := ⟨_, hz, hzb⟩
  have := h.endpoint_bijOn.injOn (Function.invFunOn_mem hex) hz
    ((Function.invFunOn_eq hex).trans hzb.symm)
  rw [this]

/-- Every position `x` of `[1, 2ml]` is an end of the pair chosen at `x`. -/
theorem MultiPairing.pair_at {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {x : ℤ}
    (h : MultiPairing m d l C) (h1 : 1 ≤ x) (h2 : x ≤ 2 * m * l) :
    (Function.invFunOn orientedEndpoint (orientedPairs (allPairs m C)) x).1 ∈ allPairs m C ∧
      ((Function.invFunOn orientedEndpoint (orientedPairs (allPairs m C)) x).1.1 = x ∨
        (Function.invFunOn orientedEndpoint (orientedPairs (allPairs m C)) x).1.2 = x) := by
  have hex : ∃ z ∈ (orientedPairs (allPairs m C) : Set ((ℤ × ℤ) × Bool)),
      orientedEndpoint z = x :=
    h.endpoint_bijOn.surjOn (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨h1, h2⟩))
  have hm := Function.invFunOn_mem hex
  have he := Function.invFunOn_eq hex
  generalize Function.invFunOn orientedEndpoint
    (orientedPairs (allPairs m C) : Set ((ℤ × ℤ) × Bool)) x = z at hm he ⊢
  rcases z with ⟨q, b⟩
  have hq : q ∈ allPairs m C := (Finset.mem_product.mp (Finset.mem_coe.mp hm)).1
  refine ⟨hq, ?_⟩
  cases b
  · left
    simpa [orientedEndpoint] using he
  · right
    simpa [orientedEndpoint] using he

/-- The sequence of a certificate: position `i` carries the difference of the pair containing it. -/
noncomputable def toSeq (m : ℕ) (C : ℕ → Finset (ℤ × ℤ)) : ℕ → ℕ :=
  fun i =>
    let z := Function.invFunOn orientedEndpoint (orientedPairs (allPairs m C)) (i : ℤ)
    (z.1.2 - z.1.1).toNat

/-- At a position `i` of `[1, 2ml]` the sequence reads `p` exactly when some pair of difference `p`
has `i` as an end. -/
theorem MultiPairing.toSeq_eq_iff {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {i p : ℕ}
    (h : MultiPairing m d l C) (hi1 : (1 : ℤ) ≤ i) (hi2 : (i : ℤ) ≤ 2 * m * l) :
    toSeq m C i = p ↔
      ∃ q ∈ allPairs m C, q.2 - q.1 = p ∧ (q.1 = i ∨ q.2 = i) := by
  obtain ⟨hq, hend⟩ := h.pair_at hi1 hi2
  simp only [toSeq]
  constructor
  · intro hp
    refine ⟨_, hq, ?_, hend⟩
    have := h.left_lt_right hq
    omega
  · rintro ⟨q, hq', hqp, hqi⟩
    rw [h.invFunOn_fst hq' hqi]
    omega

/-- The bridge: the sequence of an `m`-colour certificate is an `m`-fold Langford sequence. -/
theorem MultiPairing.isLangford {m d l : ℕ} {C : ℕ → Finset (ℤ × ℤ)}
    (h : MultiPairing m (d : ℤ) (l : ℤ) C) : Langford.IsLangford m d l (toSeq m C) := by
  have hK : ((2 * m * l : ℕ) : ℤ) = 2 * (m : ℤ) * (l : ℤ) := by push_cast; ring
  unfold Langford.IsLangford
  generalize 2 * m * l = K at hK ⊢
  refine ⟨fun i hi1 hi2 => ?_, fun p hp1 hp2 => ?_⟩
  · have hx1 : (1 : ℤ) ≤ i := by exact_mod_cast hi1
    have hx2 : (i : ℤ) ≤ 2 * (m : ℤ) * (l : ℤ) := by omega
    obtain ⟨hq, -⟩ := h.pair_at hx1 hx2
    have := h.diff_mem hq
    simp only [toSeq]
    omega
  · classical
    have hF : ((allPairs m C).filter (fun q => q.2 - q.1 = (p : ℤ))).card = m :=
      h.card_fiber (by exact_mod_cast hp1) (by omega)
    have hFmem : ∀ q, q ∈ (allPairs m C).filter (fun q => q.2 - q.1 = (p : ℤ)) ↔
        q ∈ allPairs m C ∧ q.2 - q.1 = (p : ℤ) := fun q => Finset.mem_filter
    refine ⟨((allPairs m C).filter (fun q => q.2 - q.1 = (p : ℤ))).image (fun q => q.1.toNat),
      ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn, hF]
      intro q hq r hr hqr
      rw [Finset.mem_coe, hFmem] at hq hr
      have := (h.ends_mem hq.1).1.1
      have := (h.ends_mem hr.1).1.1
      simp only at hqr
      exact Prod.ext (by omega) (by omega)
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      rw [hFmem] at hq
      have he := h.ends_mem hq.1
      refine ⟨by omega, by omega, ?_⟩
      intro hmem
      obtain ⟨r, hr, hrq⟩ := Finset.mem_image.mp hmem
      rw [hFmem] at hr
      have her := h.ends_mem hr.1
      have h12 : r.1 = q.2 := by omega
      have hinj := h.endpoint_bijOn.injOn (x₁ := (r, false)) (x₂ := (q, true))
        (by simp [orientedPairs, hr.1]) (by simp [orientedPairs, hq.1])
        (by simp [orientedEndpoint, h12])
      simp at hinj
    · intro i hi1 hi2
      have hx1 : (1 : ℤ) ≤ i := by exact_mod_cast hi1
      have hx2 : (i : ℤ) ≤ 2 * (m : ℤ) * (l : ℤ) := by omega
      rw [h.toSeq_eq_iff hx1 hx2]
      simp only [Finset.mem_image, hFmem]
      constructor
      · rintro ⟨q, hq, hqp, hqi | hqi⟩
        · left
          exact ⟨q, ⟨hq, hqp⟩, by omega⟩
        · right
          exact ⟨q.1.toNat, ⟨q, ⟨hq, hqp⟩, rfl⟩, by have := (h.ends_mem hq).1.1; omega⟩
      · rintro (⟨q, ⟨hq, hqp⟩, hqi⟩ | ⟨a, ⟨q, ⟨hq, hqp⟩, rfl⟩, hi⟩)
        · exact ⟨q, hq, hqp, Or.inl (by have := (h.ends_mem hq).1.1; omega)⟩
        · exact ⟨q, hq, hqp, Or.inr (by have := (h.ends_mem hq).1.1; omega)⟩

end
end L2
