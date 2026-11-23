import Mathlib
import ReciprocityTheory.SemistableReduction.GaussValExists

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

theorem gauss_val_le_iff_div_mem {U : Type} [Field U] (V : ValuationSubring U) {x y : U} (hy : y ≠ 0) :
    V.valuation x ≤ V.valuation y ↔ x / y ∈ V := by
  have hy0 : (0 : _) < V.valuation y := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy)
  rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ hy0]

theorem gauss_exists_div_aeval {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (hgen : IntermediateField.adjoin Ω (Set.range t) = ⊤) (z : U) :
    ∃ p q : MvPolynomial σ Ω, aeval t q ≠ 0 ∧ z = aeval t p / aeval t q := by
  have hz : z ∈ IntermediateField.adjoin Ω (Set.range t) := by rw [hgen]; trivial
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  rw [Algebra.adjoin_range_eq_range_aeval] at hr hs
  obtain ⟨p, rfl⟩ := hr
  obtain ⟨q, rfl⟩ := hs
  by_cases hq : aeval t q = 0
  · refine ⟨0, 1, by simp, ?_⟩
    simp [hq]
  · exact ⟨p, q, hq, rfl⟩

theorem gauss_nonunits {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] (V : ValuationSubring U)
    (w : Ω) : algebraMap Ω U w ∈ V.nonunits ↔ w ∈ (V.comap (algebraMap Ω U)).nonunits := by
  have key : ∀ (A : ValuationSubring U) (x : U), x ∈ A.nonunits ↔ (x = 0 ∨ x⁻¹ ∉ A) := by
    intro A x
    rw [A.mem_nonunits_iff]
    by_cases hx : x = 0
    · simp [hx]
    · have hv : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
      simp only [hx, false_or, ← A.valuation_le_one_iff, map_inv₀, not_le]
      constructor
      · intro h; exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hv, h⟩
      · intro h; exact (one_lt_inv_iff₀.mp h).2
  have key' : ∀ (A : ValuationSubring Ω) (x : Ω), x ∈ A.nonunits ↔ (x = 0 ∨ x⁻¹ ∉ A) := by
    intro A x
    rw [A.mem_nonunits_iff]
    by_cases hx : x = 0
    · simp [hx]
    · have hv : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
      simp only [hx, false_or, ← A.valuation_le_one_iff, map_inv₀, not_le]
      constructor
      · intro h; exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hv, h⟩
      · intro h; exact (one_lt_inv_iff₀.mp h).2
  rw [key, key', ValuationSubring.mem_comap, map_inv₀]
  simp

theorem gauss_unif {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (hgen : IntermediateField.adjoin Ω (Set.range t) = ⊤)
    (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (ϖ : Ω) (hdiv : ∀ y ∈ (V.comap (algebraMap Ω U)).nonunits,
      y / ϖ ∈ V.comap (algebraMap Ω U)) (z : U) (hz : z ∈ V.nonunits) :
    z / algebraMap Ω U ϖ ∈ V := by
  classical
  set W := V.comap (algebraMap Ω U) with hWdef
  by_cases hϖ : ϖ = 0
  · simp [hϖ]
  have hϖ' : algebraMap Ω U ϖ ≠ 0 := by simpa using hϖ
  obtain ⟨p, q, hq, rfl⟩ := gauss_exists_div_aeval t hgen z
  have hP := gauss_val t V ht hind p
  have hQ := gauss_val t V ht hind q
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hqs : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hq0
  obtain ⟨β, hβ, hβeq⟩ := Finset.exists_mem_eq_sup q.support hqs
    (fun α => V.valuation (algebraMap Ω U (q.coeff α)))
  have hqβ : q.coeff β ≠ 0 := MvPolynomial.mem_support_iff.mp hβ
  have hqβ' : algebraMap Ω U (q.coeff β) ≠ 0 := by simpa using hqβ
  have hvQ : V.valuation (aeval t q) = V.valuation (algebraMap Ω U (q.coeff β)) := hQ.trans hβeq
  have hvQpos : (0 : _) < V.valuation (aeval t q) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hq)
  have hzlt : V.valuation (aeval t p) < V.valuation (aeval t q) := by
    have := (V.mem_nonunits_iff).mp hz
    rwa [map_div₀, div_lt_one₀ hvQpos] at this
  rw [← gauss_val_le_iff_div_mem V hϖ', map_div₀, div_le_iff₀ hvQpos]
  rw [hP, Finset.sup_le_iff]
  intro α hα
  have hle : V.valuation (algebraMap Ω U (p.coeff α)) ≤ V.valuation (aeval t p) := by
    rw [hP]; exact Finset.le_sup (f := fun α => V.valuation (algebraMap Ω U (p.coeff α))) hα
  have hnu : algebraMap Ω U (p.coeff α / q.coeff β) ∈ V.nonunits := by
    rw [V.mem_nonunits_iff, map_div₀, map_div₀, ← hvQ, div_lt_one₀ hvQpos]
    exact lt_of_le_of_lt hle hzlt
  have hnuW : p.coeff α / q.coeff β ∈ W.nonunits := (gauss_nonunits V _).mp hnu
  have hdivW := hdiv _ hnuW
  have hmem : algebraMap Ω U (p.coeff α / q.coeff β) / algebraMap Ω U ϖ ∈ V := by
    rw [← map_div₀]; exact hdivW
  have := (gauss_val_le_iff_div_mem V hϖ').mpr hmem
  rw [map_div₀, map_div₀, ← hvQ, div_le_iff₀ hvQpos] at this
  rw [hvQ] at this ⊢
  first
  | exact this
  | exact this.trans_eq (mul_comm _ _)

end ReciprocityTheory.MultiplicativeHeights
