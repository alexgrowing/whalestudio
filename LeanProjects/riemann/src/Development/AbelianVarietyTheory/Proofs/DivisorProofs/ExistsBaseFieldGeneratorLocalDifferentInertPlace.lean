import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.InertDifferentGen

theorem exists_mul_valuation_eq_one {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0) :
    ∃ δ ∈ J⁻¹, ∃ z ∈ J, w.valuation E (δ * z) = 1 := by
  by_contra h
  push Not at h
  have h1 : J⁻¹ * J = 1 := inv_mul_cancel₀ hJ
  have hone : (1 : E) ∈ J⁻¹ * J := by rw [h1]; exact FractionalIdeal.one_mem_one _
  have key : w.valuation E (1 : E) < 1 := by
    refine FractionalIdeal.mul_induction_on (C := fun x => w.valuation E x < 1) hone ?_ ?_
    · intro a ha b hb
      have hm : a * b ∈ J⁻¹ * J := FractionalIdeal.mul_mem_mul ha hb
      rw [h1, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨x, hx⟩ := hm
      refine lt_of_le_of_ne ?_ (h a ha b hb)
      rw [← hx]
      exact w.valuation_le_one x
    · intro x y hx hy
      exact Valuation.map_add_lt _ hx hy
  simp at key

theorem mem_dual_one_iff {E : Type} [Field E] [NumberField E] (e : E) :
    e ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e)) := by
  rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (𝓞 E)⁰ E))]
  constructor
  · intro h o
    obtain ⟨k, hk⟩ := h (o : E) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply, mul_comm] at hk
    rw [← hk]
    exact isIntegral_algebraMap
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h o)
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, mul_comm]
    exact hk

theorem exists_generator_different_of_isInertAt :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∃ t : F, t ≠ 0 ∧ ∃ s₁ s₂ : E, w.valuation E s₁ = 1 ∧ w.valuation E s₂ = 1 ∧
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) := by
  intro F E _ _ _ _ _ v w hin
  have hJ : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  obtain ⟨δ, hδ, z, hz, hδz⟩ := exists_mul_valuation_eq_one w _ hJ
  obtain ⟨t, ht⟩ := v.valuation_surjective F (w.valuation E δ)
  rw [← GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt F E v w hin] at ht
  have hδ0 : w.valuation E δ ≠ 0 := by
    intro h0
    rw [map_mul, h0, zero_mul] at hδz
    exact zero_ne_one hδz
  have htE : algebraMap F E t ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ht
    exact hδ0 ht.symm
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact htE (map_zero _)
  refine ⟨t, ht0, δ / algebraMap F E t, algebraMap F E t * z, ?_, ?_, ?_, ?_⟩
  · rw [map_div₀, ht, div_self hδ0]
  · rw [map_mul, ht, ← map_mul, hδz]
  · intro e he
    rw [div_mul_cancel₀ _ htE]
    have hm := FractionalIdeal.mul_mem_mul hδ ((mem_dual_one_iff e).2 he)
    rw [inv_mul_cancel₀ hJ, FractionalIdeal.mem_one_iff] at hm
    exact hm
  · rw [mul_comm (algebraMap F E t) z, mul_inv_cancel_right₀ htE]
    exact (mem_dual_one_iff z).1 hz

end GlobalTheory.InertDifferentGen
