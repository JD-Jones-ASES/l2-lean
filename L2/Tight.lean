import L2.Multi

/-!
# The tight line for every multiplicity

For `l = 2d₀ − 1` the ordinary Langford sequence of defect `d₀` and order `l` whose pairs all
straddle the middle (Table 1 of the source) has its left ends on `[1, l]` and its right ends on
`[l + 1, 2l]`. Taking `m` copies, the `c`-th with left ends shifted by `cl` and right ends by
`(m − 1 + c)l`, gives an `m`-fold Langford sequence of order `l` and defect
`d = m(2d₀ − 1) − (d₀ − 1)`, which is the tight case `2d + l = 2ml + 1`.
-/

namespace L2
noncomputable section

/-- Table 1 as pairs: `(d₀ − r, 2d₀ + r)` for `0 ≤ r ≤ d₀ − 1` and `(2d₀ − 1 − r, 3d₀ + r)` for
`0 ≤ r ≤ d₀ − 2`; an ordinary Langford sequence of defect `d₀` and order `2d₀ − 1`, all pairs
straddling the middle. -/
def table1 (d₀ : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc 0 (d₀ - 1)).image (fun r => (d₀ - r, 2 * d₀ + r)) ∪
    (Finset.Icc 0 (d₀ - 2)).image (fun r => (2 * d₀ - 1 - r, 3 * d₀ + r))

/-- Colour `c` of the `m`-fold tight sequence of order `l = 2d₀ − 1`: copy `c` of Table 1 with left
ends shifted by `c·l` and right ends by `(m − 1 + c)·l`. -/
def tightColour (m : ℕ) (d₀ : ℤ) (c : ℕ) : Finset (ℤ × ℤ) :=
  (table1 d₀).image fun q => (q.1 + c * (2 * d₀ - 1), q.2 + (m - 1 + c) * (2 * d₀ - 1))

/-- The blocks `[cl + 1, cl + l]`, `c < m`, cover `[1, ml]`. -/
theorem exists_block (m : ℕ) (l x : ℤ) (hl : 1 ≤ l) (h1 : 1 ≤ x) (h2 : x ≤ m * l) :
    ∃ c < m, (c : ℤ) * l + 1 ≤ x ∧ x ≤ (c : ℤ) * l + l := by
  have _ := hl
  induction m with
  | zero => simp at h2; omega
  | succ n ih =>
    by_cases hx : x ≤ (n : ℤ) * l
    · obtain ⟨c, hc, hc1, hc2⟩ := ih hx
      exact ⟨c, by omega, hc1, hc2⟩
    · refine ⟨n, by omega, by omega, ?_⟩
      have h3 : ((n + 1 : ℕ) : ℤ) * l = (n : ℤ) * l + l := by push_cast; ring
      omega

namespace Tight

/-- The differences of a collection whose left ends are shifted by `a` and right ends by `b` are
the original differences shifted by `b − a`. -/
theorem mem_pairDifferences_image_shift (T : Finset (ℤ × ℤ)) (a b x : ℤ) :
    x ∈ pairDifferences (T.image fun q => (q.1 + a, q.2 + b)) ↔
      x - (b - a) ∈ pairDifferences T := by
  simp only [pairDifferences, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, by ring⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨_, ⟨q, hq, rfl⟩, by linarith⟩

/-- The endpoints of a collection whose left ends are shifted by `a` and right ends by `b`: a
shifted left end or a shifted right end. -/
theorem mem_pairEndpoints_image_shift (T : Finset (ℤ × ℤ)) (a b x : ℤ) :
    x ∈ pairEndpoints (T.image fun q => (q.1 + a, q.2 + b)) ↔
      x - a ∈ T.image Prod.fst ∨ x - b ∈ T.image Prod.snd := by
  simp only [pairEndpoints, Finset.mem_biUnion, Finset.mem_image, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, hx | hx⟩
    · exact Or.inl ⟨q, hq, by rw [hx]; ring⟩
    · exact Or.inr ⟨q, hq, by rw [hx]; ring⟩
  · rintro (⟨q, hq, h⟩ | ⟨q, hq, h⟩)
    · exact ⟨_, ⟨q, hq, rfl⟩, Or.inl (by linarith)⟩
    · exact ⟨_, ⟨q, hq, rfl⟩, Or.inr (by linarith)⟩

/-- The endpoints of a union of colour classes are the endpoints of the individual classes. -/
theorem mem_pairEndpoints_biUnion (S : Finset ℕ) (C : ℕ → Finset (ℤ × ℤ)) (x : ℤ) :
    x ∈ pairEndpoints (S.biUnion C) ↔ ∃ c ∈ S, x ∈ pairEndpoints (C c) := by
  simp only [pairEndpoints, Finset.mem_biUnion]
  constructor
  · rintro ⟨p, ⟨c, hc, hp⟩, hx⟩
    exact ⟨c, hc, p, hp, hx⟩
  · rintro ⟨c, hc, p, hp, hx⟩
    exact ⟨p, ⟨c, hc, hp⟩, hx⟩

/-- The differences of Table 1 are `d₀, d₀ + 1, …, 3d₀ − 2`: `d₀ + 2r` from the first family and
`d₀ + 1 + 2r` from the second. -/
theorem pairDifferences_table1 (d₀ : ℤ) :
    pairDifferences (table1 d₀) = Finset.Icc d₀ (3 * d₀ - 2) := by
  ext x
  simp only [pairDifferences, table1, Finset.image_union, Finset.image_image, Finset.mem_union,
    Finset.mem_image, Finset.mem_Icc, Function.comp_apply]
  constructor
  · rintro (⟨r, ⟨h1, h2⟩, rfl⟩ | ⟨r, ⟨h1, h2⟩, rfl⟩) <;> omega
  · intro h
    rcases Int.emod_two_eq_zero_or_one (x - d₀) with he | he
    · exact Or.inl ⟨(x - d₀) / 2, ⟨by omega, by omega⟩, by omega⟩
    · exact Or.inr ⟨(x - d₀ - 1) / 2, ⟨by omega, by omega⟩, by omega⟩

/-- The left ends of Table 1 fill `[1, 2d₀ − 1]`. -/
theorem image_fst_table1 (d₀ : ℤ) :
    (table1 d₀).image Prod.fst = Finset.Icc 1 (2 * d₀ - 1) := by
  ext x
  simp only [table1, Finset.image_union, Finset.image_image, Finset.mem_union,
    Finset.mem_image, Finset.mem_Icc, Function.comp_apply]
  constructor
  · rintro (⟨r, ⟨h1, h2⟩, rfl⟩ | ⟨r, ⟨h1, h2⟩, rfl⟩) <;> omega
  · intro h
    by_cases hx : x ≤ d₀
    · exact Or.inl ⟨d₀ - x, ⟨by omega, by omega⟩, by omega⟩
    · exact Or.inr ⟨2 * d₀ - 1 - x, ⟨by omega, by omega⟩, by omega⟩

/-- The right ends of Table 1 fill `[2d₀, 4d₀ − 2]`. -/
theorem image_snd_table1 (d₀ : ℤ) :
    (table1 d₀).image Prod.snd = Finset.Icc (2 * d₀) (4 * d₀ - 2) := by
  ext x
  simp only [table1, Finset.image_union, Finset.image_image, Finset.mem_union,
    Finset.mem_image, Finset.mem_Icc, Function.comp_apply]
  constructor
  · rintro (⟨r, ⟨h1, h2⟩, rfl⟩ | ⟨r, ⟨h1, h2⟩, rfl⟩) <;> omega
  · intro h
    by_cases hx : x < 3 * d₀
    · exact Or.inl ⟨x - 2 * d₀, ⟨by omega, by omega⟩, by omega⟩
    · exact Or.inr ⟨x - 3 * d₀, ⟨by omega, by omega⟩, by omega⟩

/-- Table 1 has at most `2d₀ − 1` pairs. -/
theorem card_table1 (d₀ : ℤ) (hd : 1 ≤ d₀) : (table1 d₀).card ≤ (2 * d₀ - 1).toNat := by
  unfold table1
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := (Finset.card_image_le (s := Finset.Icc 0 (d₀ - 1))
    (f := fun r => (d₀ - r, 2 * d₀ + r)))
  have h2 := (Finset.card_image_le (s := Finset.Icc 0 (d₀ - 2))
    (f := fun r => (2 * d₀ - 1 - r, 3 * d₀ + r)))
  rw [Int.card_Icc] at h1 h2
  omega

end Tight

open Tight in
/-- The tight line: `m` interleaved copies of Table 1 form an `m`-fold Langford sequence of order
`2d₀ − 1` and defect `m(2d₀ − 1) − (d₀ − 1)`. -/
theorem tight_multi (m : ℕ) (d₀ : ℤ) (hm : 1 ≤ m) (hd : 1 ≤ d₀) :
    MultiPairing m (m * (2 * d₀ - 1) - (d₀ - 1)) (2 * d₀ - 1) (tightColour m d₀) := by
  have hM1 : (2 * d₀ - 1) ≤ (m : ℤ) * (2 * d₀ - 1) := by
    have : (1 : ℤ) ≤ m := by exact_mod_cast hm
    nlinarith
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · -- the differences of colour `c` are `[d, d + l − 1]`
    intro c _
    ext x
    unfold tightColour
    rw [mem_pairDifferences_image_shift, pairDifferences_table1 d₀]
    have hB : ((m : ℤ) - 1 + c) * (2 * d₀ - 1) - (c : ℤ) * (2 * d₀ - 1)
        = (m : ℤ) * (2 * d₀ - 1) - (2 * d₀ - 1) := by ring
    rw [hB]
    generalize (m : ℤ) * (2 * d₀ - 1) = M
    simp only [Finset.mem_Icc]
    omega
  · -- the endpoints of all colours fill `[1, 2ml]`
    ext x
    rw [mem_pairEndpoints_biUnion, Finset.mem_Icc]
    have key : ∀ c : ℕ, x ∈ pairEndpoints (tightColour m d₀ c) ↔
        ((c : ℤ) * (2 * d₀ - 1) + 1 ≤ x ∧ x ≤ (c : ℤ) * (2 * d₀ - 1) + (2 * d₀ - 1)) ∨
        ((c : ℤ) * (2 * d₀ - 1) + (m : ℤ) * (2 * d₀ - 1) + 1 ≤ x ∧
          x ≤ (c : ℤ) * (2 * d₀ - 1) + (m : ℤ) * (2 * d₀ - 1) + (2 * d₀ - 1)) := by
      intro c
      unfold tightColour
      rw [mem_pairEndpoints_image_shift, image_fst_table1, image_snd_table1]
      have hB : ((m : ℤ) - 1 + c) * (2 * d₀ - 1)
          = (c : ℤ) * (2 * d₀ - 1) + (m : ℤ) * (2 * d₀ - 1) - (2 * d₀ - 1) := by ring
      rw [hB]
      generalize (m : ℤ) * (2 * d₀ - 1) = M
      generalize (c : ℤ) * (2 * d₀ - 1) = A
      simp only [Finset.mem_Icc]
      omega
    have h2m : (2 * (m : ℤ)) * (2 * d₀ - 1) = 2 * ((m : ℤ) * (2 * d₀ - 1)) := by ring
    rw [h2m]
    constructor
    · rintro ⟨c, hc, hx⟩
      rw [Finset.mem_range] at hc
      rw [key] at hx
      have hA0 : 0 ≤ (c : ℤ) * (2 * d₀ - 1) := by
        have : (0 : ℤ) ≤ c := by exact_mod_cast Nat.zero_le c
        nlinarith
      have hAM : (c : ℤ) * (2 * d₀ - 1) + (2 * d₀ - 1) ≤ (m : ℤ) * (2 * d₀ - 1) := by
        have : (c : ℤ) + 1 ≤ m := by exact_mod_cast hc
        nlinarith
      omega
    · rintro ⟨h1, h2⟩
      by_cases hx : x ≤ (m : ℤ) * (2 * d₀ - 1)
      · obtain ⟨c, hc, hc1, hc2⟩ := exists_block m (2 * d₀ - 1) x (by omega) h1 hx
        exact ⟨c, Finset.mem_range.2 hc, (key c).2 (Or.inl ⟨hc1, hc2⟩)⟩
      · obtain ⟨c, hc, hc1, hc2⟩ :=
          exists_block m (2 * d₀ - 1) (x - (m : ℤ) * (2 * d₀ - 1)) (by omega) (by omega)
            (by omega)
        exact ⟨c, Finset.mem_range.2 hc, (key c).2 (Or.inr ⟨by omega, by omega⟩)⟩
  · -- at most `ml` pairs in all
    calc ∑ c ∈ Finset.range m, (tightColour m d₀ c).card
        ≤ ∑ _c ∈ Finset.range m, (2 * d₀ - 1).toNat :=
          Finset.sum_le_sum fun c _ => Finset.card_image_le.trans (card_table1 d₀ hd)
      _ = m * (2 * d₀ - 1).toNat := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end
end L2
