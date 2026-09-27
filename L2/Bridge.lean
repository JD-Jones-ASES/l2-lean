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

/-- A certificate has exactly `ml` pairs. -/
theorem MultiPairing.card_allPairs {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)}
    (h : MultiPairing m d l C) : (allPairs m C).card = m * l.toNat := by
  sorry

/-- Every position of `[1, 2ml]` is exactly one oriented end of one pair. -/
theorem MultiPairing.endpoint_bijOn {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)}
    (h : MultiPairing m d l C) :
    Set.BijOn orientedEndpoint (orientedPairs (allPairs m C)) (Finset.Icc 1 (2 * m * l)) := by
  sorry

/-- Every colour has exactly `l` pairs. -/
theorem MultiPairing.card_colour {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {c : ℕ}
    (h : MultiPairing m d l C) (hc : c < m) : (C c).card = l.toNat := by
  sorry

/-- Distinct colours share no pair. -/
theorem MultiPairing.pairwise_disjoint {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {c c' : ℕ}
    (h : MultiPairing m d l C) (hc : c < m) (hc' : c' < m) (hne : c ≠ c') :
    Disjoint (C c) (C c') := by
  sorry

/-- Within a colour, distinct pairs have distinct differences. -/
theorem MultiPairing.diff_injOn {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {c : ℕ}
    (h : MultiPairing m d l C) (hc : c < m) :
    Set.InjOn (fun q : ℤ × ℤ => q.2 - q.1) (C c) := by
  sorry

/-- Exactly `m` pairs of the certificate have difference `p`, for every `p ∈ [d, d + l − 1]`. -/
theorem MultiPairing.card_fiber {m : ℕ} {d l : ℤ} {C : ℕ → Finset (ℤ × ℤ)} {p : ℤ}
    (h : MultiPairing m d l C) (hp : d ≤ p) (hp' : p ≤ d + l - 1) :
    ((allPairs m C).filter (fun q => q.2 - q.1 = p)).card = m := by
  sorry

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

/-- The sequence of a certificate: position `i` carries the difference of the pair containing it. -/
noncomputable def toSeq (m : ℕ) (C : ℕ → Finset (ℤ × ℤ)) : ℕ → ℕ :=
  fun i =>
    let z := Function.invFunOn orientedEndpoint (orientedPairs (allPairs m C)) (i : ℤ)
    (z.1.2 - z.1.1).toNat

/-- The bridge: the sequence of an `m`-colour certificate is an `m`-fold Langford sequence. -/
theorem MultiPairing.isLangford {m d l : ℕ} {C : ℕ → Finset (ℤ × ℤ)}
    (h : MultiPairing m (d : ℤ) (l : ℤ) C) : Langford.IsLangford m d l (toSeq m C) := by
  sorry

end
end L2
