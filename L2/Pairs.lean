import Mathlib

/-!
# Pairs of positions

A Langford-type certificate is a finite set of pairs `(x, y)` of integer positions. This file
collects the endpoints and the differences of such a set, translation of all pairs by a constant,
and the oriented endpoints: each pair has a left and a right end, and the map sending an oriented
pair to its end is the bridge between a set of pairs and a sequence.

Adapted from the gn-lean development (PALOMAR-2026-09-07-000013, MIT, the same author) and ported to
Lean v4.35.0-rc2.
-/

namespace L2
noncomputable section

/-- The positions occupied by a finite collection of pairs. -/
def pairEndpoints (ps : Finset (ℤ × ℤ)) : Finset ℤ :=
  ps.biUnion fun p => {p.1, p.2}

/-- The differences `y − x` of the pairs `(x, y)` of a finite collection. -/
def pairDifferences (ps : Finset (ℤ × ℤ)) : Finset ℤ :=
  ps.image fun p => p.2 - p.1

/-- The endpoints of a union are the union of the endpoints. -/
@[simp] theorem pairEndpoints_union (ps qs : Finset (ℤ × ℤ)) :
    pairEndpoints (ps ∪ qs) = pairEndpoints ps ∪ pairEndpoints qs := by
  ext x
  simp [pairEndpoints]
  aesop

/-- The endpoints of one pair. -/
@[simp] theorem pairEndpoints_singleton (a b : ℤ) :
    pairEndpoints {(a, b)} = {a, b} := by
  simp [pairEndpoints]

/-- The differences of a union are the union of the differences. -/
@[simp] theorem pairDifferences_union (ps qs : Finset (ℤ × ℤ)) :
    pairDifferences (ps ∪ qs) = pairDifferences ps ∪ pairDifferences qs := by
  exact Finset.image_union _ _

/-- The difference of one pair. -/
@[simp] theorem pairDifferences_singleton (a b : ℤ) :
    pairDifferences {(a, b)} = {b - a} := by
  simp [pairDifferences]

/-- Cardinality bounds add over a union. -/
theorem card_union_le_of_le {ps qs : Finset (ℤ × ℤ)} {m n : ℕ}
    (hp : ps.card ≤ m) (hq : qs.card ≤ n) : (ps ∪ qs).card ≤ m + n :=
  (Finset.card_union_le ps qs).trans (Nat.add_le_add hp hq)

/-- Translate every pair by `c`. -/
def shiftPairs (c : ℤ) (ps : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  ps.image fun p => (p.1 + c, p.2 + c)

/-- The endpoints of a translated collection are the translated endpoints. -/
theorem mem_pairEndpoints_shiftPairs (c : ℤ) (ps : Finset (ℤ × ℤ)) (x : ℤ) :
    x ∈ pairEndpoints (shiftPairs c ps) ↔ x - c ∈ pairEndpoints ps := by
  simp only [pairEndpoints, shiftPairs, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx⟩
    refine ⟨q, hq, ?_⟩
    rcases hx with hx | hx
    · left; omega
    · right; omega
  · rintro ⟨q, hq, hx⟩
    refine ⟨_, ⟨q, hq, rfl⟩, ?_⟩
    rcases hx with hx | hx
    · left; dsimp only; omega
    · right; dsimp only; omega

/-- Translation preserves the differences. -/
theorem pairDifferences_shiftPairs (c : ℤ) (ps : Finset (ℤ × ℤ)) :
    pairDifferences (shiftPairs c ps) = pairDifferences ps := by
  unfold pairDifferences shiftPairs
  rw [Finset.image_image]
  congr 1
  funext p
  change (p.2 + c) - (p.1 + c) = p.2 - p.1
  ring

/-- Translation does not increase the number of pairs. -/
theorem card_shiftPairs_le (c : ℤ) (ps : Finset (ℤ × ℤ)) :
    (shiftPairs c ps).card ≤ ps.card :=
  Finset.card_image_le

/-- Each pair has two oriented endpoints. -/
def orientedPairs (ps : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × Bool) :=
  ps ×ˢ Finset.univ

/-- The end of a pair selected by an orientation: the right end for `true`, the left for `false`. -/
def orientedEndpoint (z : (ℤ × ℤ) × Bool) : ℤ :=
  if z.2 then z.1.2 else z.1.1

/-- The other end of the same pair. -/
def flipEndpoint (z : (ℤ × ℤ) × Bool) : (ℤ × ℤ) × Bool := (z.1, !z.2)

/-- The oriented endpoints of a collection run over its endpoints. -/
theorem orientedEndpoint_image (ps : Finset (ℤ × ℤ)) :
    (orientedPairs ps).image orientedEndpoint = pairEndpoints ps := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨p, b⟩, hz, heq⟩ := Finset.mem_image.mp hx
    have hp : p ∈ ps := (Finset.mem_product.mp hz).1
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hp, ?_⟩
    cases b <;> simp only [orientedEndpoint, Bool.false_eq_true, ↓reduceIte] at heq
    · exact Finset.mem_insert.mpr (Or.inl heq.symm)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr heq.symm))
  · intro hx
    obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxp
    rcases hxp with hx | hx
    · exact Finset.mem_image.mpr ⟨(p, false), by simp [orientedPairs, hp], hx.symm⟩
    · exact Finset.mem_image.mpr ⟨(p, true), by simp [orientedPairs, hp], hx.symm⟩

/-- Flipping the orientation twice is the identity. -/
theorem flipEndpoint_involutive : Function.Involutive flipEndpoint := by
  rintro ⟨p, b⟩
  cases b <;> rfl

/-- Flipping the orientation permutes the oriented pairs of a collection. -/
theorem flipEndpoint_bijOn (ps : Finset (ℤ × ℤ)) :
    Set.BijOn flipEndpoint (orientedPairs ps) (orientedPairs ps) := by
  have hmap : Set.MapsTo flipEndpoint (orientedPairs ps) (orientedPairs ps) := by
    intro z hz
    have hp := (Finset.mem_product.mp hz).1
    simp [flipEndpoint, orientedPairs, hp]
  refine ⟨hmap, flipEndpoint_involutive.injective.injOn, ?_⟩
  intro z hz
  exact ⟨flipEndpoint z, hmap hz, flipEndpoint_involutive z⟩

/-- A collection of `k` pairs has `2k` oriented pairs. -/
theorem card_orientedPairs (ps : Finset (ℤ × ℤ)) :
    (orientedPairs ps).card = 2 * ps.card := by
  simp [orientedPairs, Finset.card_product, mul_comm]

/-- A collection of `k` pairs occupies at most `2k` positions. -/
theorem card_pairEndpoints_le (ps : Finset (ℤ × ℤ)) :
    (pairEndpoints ps).card ≤ 2 * ps.card := by
  rw [← orientedEndpoint_image, ← card_orientedPairs]
  exact Finset.card_image_le

end
end L2
