import L2.Pairs

/-!
# Certificates for multi-fold Langford sequences

An `m`-fold Langford sequence of order `l` and defect `d` is certified by `m` colour classes of
pairs of positions: in each colour the differences are exactly `[d, d + l − 1]`, the endpoints of all
colours together cover `[1, 2ml]`, and there are at most `ml` pairs in all. Counting then forces
every colour to have one pair of each difference and every position to be used once; that
bookkeeping is done once, in the bridge to the sequence form. This file has the two-colour case
used for `m = 2`, concatenation of two-fold certificates, and juxtaposition of an `m₁`-fold and an
`m₂`-fold certificate.
-/

namespace L2
noncomputable section

/-- A two-colour certificate for a two-fold Langford sequence of order `l` and defect `d`. -/
structure TwoFold (d l : ℤ) (A B : Finset (ℤ × ℤ)) : Prop where
  defect_pos : 1 ≤ d
  order_pos : 1 ≤ l
  diffA : pairDifferences A = Finset.Icc d (d + l - 1)
  diffB : pairDifferences B = Finset.Icc d (d + l - 1)
  endpoints : pairEndpoints (A ∪ B) = Finset.Icc 1 (4 * l)
  cardA : A.card ≤ l.toNat
  cardB : B.card ≤ l.toNat

/-- An `m`-colour certificate for an `m`-fold Langford sequence of order `l` and defect `d`. -/
structure MultiPairing (m : ℕ) (d l : ℤ) (C : ℕ → Finset (ℤ × ℤ)) : Prop where
  defect_pos : 1 ≤ d
  order_pos : 1 ≤ l
  differences : ∀ c < m, pairDifferences (C c) = Finset.Icc d (d + l - 1)
  endpoints : pairEndpoints ((Finset.range m).biUnion C) = Finset.Icc 1 (2 * m * l)
  card_le : ∑ c ∈ Finset.range m, (C c).card ≤ m * l.toNat

/-- A two-colour certificate is a `2`-colour certificate. -/
theorem TwoFold.toMulti {d l : ℤ} {A B : Finset (ℤ × ℤ)} (h : TwoFold d l A B) :
    MultiPairing 2 d l (fun c => if c = 0 then A else B) := by
  have hU : (Finset.range 2).biUnion (fun c => if c = 0 then A else B) = A ∪ B := by
    ext q
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union]
    constructor
    · rintro ⟨c, hc, hq⟩
      interval_cases c
      · exact Or.inl (by simpa using hq)
      · exact Or.inr (by simpa using hq)
    · rintro (hq | hq)
      · exact ⟨0, by norm_num, by simpa using hq⟩
      · exact ⟨1, by norm_num, by simpa using hq⟩
  refine ⟨h.defect_pos, h.order_pos, ?_, ?_, ?_⟩
  · intro c hc
    interval_cases c
    · simpa using h.diffA
    · simpa using h.diffB
  · rw [hU, h.endpoints]
    congr 1
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [zero_add, ↓reduceIte, one_ne_zero]
    have := h.cardA
    have := h.cardB
    omega

/-- Concatenation: a certificate for `(d, l₁)` followed by one for `(d + l₁, l₂)`, shifted by `4l₁`,
is a certificate for `(d, l₁ + l₂)`. -/
theorem TwoFold.concat {d l₁ l₂ : ℤ} {A₁ B₁ A₂ B₂ : Finset (ℤ × ℤ)} (h₁ : TwoFold d l₁ A₁ B₁)
    (h₂ : TwoFold (d + l₁) l₂ A₂ B₂) :
    TwoFold d (l₁ + l₂) (A₁ ∪ shiftPairs (4 * l₁) A₂) (B₁ ∪ shiftPairs (4 * l₁) B₂) := by
  have hl₁ := h₁.order_pos
  have hl₂ := h₂.order_pos
  have hdiff : Finset.Icc d (d + l₁ - 1) ∪ Finset.Icc (d + l₁) (d + l₁ + l₂ - 1) =
      Finset.Icc d (d + (l₁ + l₂) - 1) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  refine ⟨h₁.defect_pos, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pairDifferences_union, pairDifferences_shiftPairs, h₁.diffA, h₂.diffA, hdiff]
  · rw [pairDifferences_union, pairDifferences_shiftPairs, h₁.diffB, h₂.diffB, hdiff]
  · ext x
    have e1 : x ∈ pairEndpoints A₁ ∨ x ∈ pairEndpoints B₁ ↔ 1 ≤ x ∧ x ≤ 4 * l₁ := by
      rw [← Finset.mem_union, ← pairEndpoints_union, h₁.endpoints, Finset.mem_Icc]
    have e2 : x - 4 * l₁ ∈ pairEndpoints A₂ ∨ x - 4 * l₁ ∈ pairEndpoints B₂ ↔
        1 ≤ x - 4 * l₁ ∧ x - 4 * l₁ ≤ 4 * l₂ := by
      rw [← Finset.mem_union, ← pairEndpoints_union, h₂.endpoints, Finset.mem_Icc]
    simp only [pairEndpoints_union, Finset.mem_union, mem_pairEndpoints_shiftPairs,
      Finset.mem_Icc]
    constructor
    · intro hx
      rcases hx with (hx | hx) | (hx | hx)
      · have := e1.mp (Or.inl hx); omega
      · have := e2.mp (Or.inl hx); omega
      · have := e1.mp (Or.inr hx); omega
      · have := e2.mp (Or.inr hx); omega
    · intro hx
      by_cases hle : x ≤ 4 * l₁
      · rcases e1.mpr ⟨hx.1, hle⟩ with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
      · rcases e2.mpr ⟨by omega, by omega⟩ with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)
  · refine (card_union_le_of_le h₁.cardA ((card_shiftPairs_le _ _).trans h₂.cardA)).trans ?_
    omega
  · refine (card_union_le_of_le h₁.cardB ((card_shiftPairs_le _ _).trans h₂.cardB)).trans ?_
    omega

/-- The endpoints of a union of colour classes are the endpoints of some class. -/
theorem mem_pairEndpoints_biUnion (s : Finset ℕ) (C : ℕ → Finset (ℤ × ℤ)) (x : ℤ) :
    x ∈ pairEndpoints (s.biUnion C) ↔ ∃ c ∈ s, x ∈ pairEndpoints (C c) := by
  simp only [pairEndpoints, Finset.mem_biUnion]
  constructor
  · rintro ⟨p, ⟨c, hc, hp⟩, hx⟩
    exact ⟨c, hc, p, hp, hx⟩
  · rintro ⟨c, hc, p, hp, hx⟩
    exact ⟨p, ⟨c, hc, hp⟩, hx⟩

/-- Juxtaposition of an `m₁`-colour and an `m₂`-colour certificate of the same order: the colours
`c < m₁` are the first certificate's, the others the second's shifted by `2m₁l`. -/
def juxtapose (m₁ : ℕ) (l : ℤ) (C₁ C₂ : ℕ → Finset (ℤ × ℤ)) : ℕ → Finset (ℤ × ℤ) :=
  fun c => if c < m₁ then C₁ c else shiftPairs (2 * m₁ * l) (C₂ (c - m₁))

/-- Juxtaposition: an `m₁`-fold and an `m₂`-fold sequence of the same order and defect, side by
side, form an `(m₁ + m₂)`-fold sequence. -/
theorem MultiPairing.juxtapose {m₁ m₂ : ℕ} {d l : ℤ} {C₁ C₂ : ℕ → Finset (ℤ × ℤ)}
    (h₁ : MultiPairing m₁ d l C₁) (h₂ : MultiPairing m₂ d l C₂) :
    MultiPairing (m₁ + m₂) d l (juxtapose m₁ l C₁ C₂) := by
  have hlo (c : ℕ) (hc : c < m₁) : L2.juxtapose m₁ l C₁ C₂ c = C₁ c := by
    simp only [L2.juxtapose, hc, ↓reduceIte]
  have hhi (c : ℕ) : L2.juxtapose m₁ l C₁ C₂ (m₁ + c) = shiftPairs (2 * m₁ * l) (C₂ c) := by
    simp only [L2.juxtapose, show ¬ (m₁ + c < m₁) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  refine ⟨h₁.defect_pos, h₁.order_pos, ?_, ?_, ?_⟩
  · intro c hc
    by_cases h : c < m₁
    · rw [hlo c h]
      exact h₁.differences c h
    · obtain ⟨k, rfl⟩ : ∃ k, c = m₁ + k := ⟨c - m₁, by omega⟩
      rw [hhi k, pairDifferences_shiftPairs]
      exact h₂.differences k (by omega)
  · ext x
    have e1 : (∃ c < m₁, x ∈ pairEndpoints (C₁ c)) ↔ 1 ≤ x ∧ x ≤ 2 * (m₁ : ℤ) * l := by
      rw [← Finset.mem_Icc, ← h₁.endpoints, mem_pairEndpoints_biUnion]
      simp only [Finset.mem_range]
    have e2 : (∃ c < m₂, x - 2 * (m₁ : ℤ) * l ∈ pairEndpoints (C₂ c)) ↔
        1 ≤ x - 2 * (m₁ : ℤ) * l ∧ x - 2 * (m₁ : ℤ) * l ≤ 2 * (m₂ : ℤ) * l := by
      rw [← Finset.mem_Icc, ← h₂.endpoints, mem_pairEndpoints_biUnion]
      simp only [Finset.mem_range]
    have split : (∃ c < m₁ + m₂, x ∈ pairEndpoints (L2.juxtapose m₁ l C₁ C₂ c)) ↔
        (∃ c < m₁, x ∈ pairEndpoints (C₁ c)) ∨
          (∃ c < m₂, x - 2 * (m₁ : ℤ) * l ∈ pairEndpoints (C₂ c)) := by
      constructor
      · rintro ⟨c, hc, hx⟩
        by_cases h : c < m₁
        · rw [hlo c h] at hx
          exact Or.inl ⟨c, h, hx⟩
        · obtain ⟨k, rfl⟩ : ∃ k, c = m₁ + k := ⟨c - m₁, by omega⟩
          rw [hhi k, mem_pairEndpoints_shiftPairs] at hx
          exact Or.inr ⟨k, by omega, hx⟩
      · rintro (⟨c, hc, hx⟩ | ⟨k, hk, hx⟩)
        · exact ⟨c, by omega, by rw [hlo c hc]; exact hx⟩
        · exact ⟨m₁ + k, by omega, by rw [hhi k, mem_pairEndpoints_shiftPairs]; exact hx⟩
    rw [mem_pairEndpoints_biUnion, Finset.mem_Icc]
    simp only [Finset.mem_range]
    rw [split, e1, e2]
    have hsum : 2 * ((m₁ + m₂ : ℕ) : ℤ) * l = 2 * (m₁ : ℤ) * l + 2 * (m₂ : ℤ) * l := by
      push_cast
      ring
    have hl := h₁.order_pos
    have ha : 0 ≤ 2 * (m₁ : ℤ) * l := mul_nonneg (by positivity) (by omega)
    have hb : 0 ≤ 2 * (m₂ : ℤ) * l := mul_nonneg (by positivity) (by omega)
    rw [hsum]
    omega
  · rw [Finset.sum_range_add]
    have e1 : ∑ c ∈ Finset.range m₁, (L2.juxtapose m₁ l C₁ C₂ c).card =
        ∑ c ∈ Finset.range m₁, (C₁ c).card :=
      Finset.sum_congr rfl fun c hc => by rw [hlo c (Finset.mem_range.mp hc)]
    have e2 : ∑ k ∈ Finset.range m₂, (L2.juxtapose m₁ l C₁ C₂ (m₁ + k)).card ≤
        ∑ k ∈ Finset.range m₂, (C₂ k).card :=
      Finset.sum_le_sum fun k _ => by rw [hhi k]; exact card_shiftPairs_le _ _
    have c1 := h₁.card_le
    have c2 := h₂.card_le
    rw [e1, add_mul]
    omega

end
end L2
