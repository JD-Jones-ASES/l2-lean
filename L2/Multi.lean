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
  sorry

/-- Juxtaposition of an `m₁`-colour and an `m₂`-colour certificate of the same order: the colours
`c < m₁` are the first certificate's, the others the second's shifted by `2m₁l`. -/
def juxtapose (m₁ : ℕ) (l : ℤ) (C₁ C₂ : ℕ → Finset (ℤ × ℤ)) : ℕ → Finset (ℤ × ℤ) :=
  fun c => if c < m₁ then C₁ c else shiftPairs (2 * m₁ * l) (C₂ (c - m₁))

/-- Juxtaposition: an `m₁`-fold and an `m₂`-fold sequence of the same order and defect, side by
side, form an `(m₁ + m₂)`-fold sequence. -/
theorem MultiPairing.juxtapose {m₁ m₂ : ℕ} {d l : ℤ} {C₁ C₂ : ℕ → Finset (ℤ × ℤ)}
    (h₁ : MultiPairing m₁ d l C₁) (h₂ : MultiPairing m₂ d l C₂) :
    MultiPairing (m₁ + m₂) d l (juxtapose m₁ l C₁ C₂) := by
  sorry

end
end L2
