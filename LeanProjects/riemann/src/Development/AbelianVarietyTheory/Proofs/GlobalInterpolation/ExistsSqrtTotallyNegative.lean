import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC
open scoped ComplexConjugate

namespace GlobalTheory.CMGen

theorem exists_integer_not_mem (K : Type) [Field K] [NumberField K] [IsCMField K] :
    ∃ x : 𝓞 K, (x : K) ∉ maximalRealSubfield K := by
  by_contra h
  push_neg at h
  apply NumberField.IsCMField.complexConj_ne_one K
  ext y
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have ha : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K a) = algebraMap (𝓞 K) K a :=
    (NumberField.IsCMField.complexConj_eq_self_iff K _).mpr (h a)
  have hb : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K b) = algebraMap (𝓞 K) K b :=
    (NumberField.IsCMField.complexConj_eq_self_iff K _).mpr (h b)
  rw [map_div₀, ha, hb, AlgEquiv.one_apply]

theorem exists_extension (K : Type) [Field K] [NumberField K] (φ : maximalRealSubfield K →+* ℝ) :
    ∃ ψ : K →+* ℂ, ∀ x : maximalRealSubfield K,
      ψ (algebraMap (maximalRealSubfield K) K x) = (φ x : ℂ) := by
  letI : Algebra (maximalRealSubfield K) ℂ := (Complex.ofRealHom.comp φ).toAlgebra
  haveI : Algebra.IsAlgebraic (maximalRealSubfield K) K := Algebra.IsAlgebraic.tower_top (K := ℚ) _
  let f : K →ₐ[maximalRealSubfield K] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, fun x => f.commutes x⟩

theorem exists_sqrt_totallyNegative : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    ∃ (d : 𝓞 (maximalRealSubfield K)) (δ : K), δ ^ 2 = algebraMap (maximalRealSubfield K) K d ∧
      δ ∉ maximalRealSubfield K ∧
      ∀ φ : maximalRealSubfield K →+* ℝ, φ (d : maximalRealSubfield K) < 0 := by
  intro K _ _ _
  obtain ⟨x, hx⟩ := exists_integer_not_mem K
  let y : 𝓞 K := x - NumberField.IsCMField.ringOfIntegersComplexConj K x
  have hy : (y : K) = (x : K) - NumberField.IsCMField.complexConj K (x : K) := by
    simp [y, NumberField.IsCMField.coe_ringOfIntegersComplexConj]
  have hconj : NumberField.IsCMField.complexConj K (y : K) = -(y : K) := by
    rw [hy, map_sub, NumberField.IsCMField.complexConj_apply_apply, neg_sub]
  have hy0 : (y : K) ≠ 0 := by
    intro h0
    apply hx
    rw [← NumberField.IsCMField.complexConj_eq_self_iff]
    rw [hy, sub_eq_zero] at h0
    exact h0.symm
  have hsq : (y : K) ^ 2 ∈ maximalRealSubfield K := by
    rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_pow, hconj, neg_sq]
  have hint : IsIntegral ℤ (⟨(y : K) ^ 2, hsq⟩ : maximalRealSubfield K) := by
    refine (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective (maximalRealSubfield K) K)).mp ?_
    change IsIntegral ℤ ((y : K) ^ 2)
    exact (RingOfIntegers.isIntegral_coe y).pow 2
  refine ⟨⟨⟨(y : K) ^ 2, hsq⟩, hint⟩, (y : K), rfl, ?_, ?_⟩
  · intro hmem
    apply hy0
    have h2 := hconj
    rw [(NumberField.IsCMField.complexConj_eq_self_iff K _).mpr hmem] at h2
    have h3 : (2 : K) * (y : K) = 0 := by rw [two_mul]; nth_rewrite 1 [h2]; ring
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h two_ne_zero
    · exact h
  · intro φ
    obtain ⟨ψ, hψ⟩ := exists_extension K φ
    have hval := hψ ⟨(y : K) ^ 2, hsq⟩
    have hψy : ψ (y : K) = ψ (x : K) - conj (ψ (x : K)) := by
      rw [hy, map_sub, NumberField.IsCMField.complexEmbedding_complexConj]
    have hne : ψ (y : K) ≠ 0 := by
      rw [map_ne_zero]; exact hy0
    have him : (ψ (x : K)).im ≠ 0 := by
      intro h0
      apply hne
      rw [hψy, Complex.sub_conj, h0]
      simp
    have key : ((φ ⟨(y : K) ^ 2, hsq⟩ : ℝ) : ℂ) = ((-(2 * (ψ (x : K)).im) ^ 2 : ℝ) : ℂ) := by
      rw [← hval]
      change ψ ((y : K) ^ 2) = _
      rw [map_pow, hψy, Complex.sub_conj]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    have key' : φ ⟨(y : K) ^ 2, hsq⟩ = -(2 * (ψ (x : K)).im) ^ 2 := by exact_mod_cast key
    show φ ⟨(y : K) ^ 2, hsq⟩ < 0
    rw [key']
    have : 0 < (2 * (ψ (x : K)).im) ^ 2 := by positivity
    linarith

end GlobalTheory.CMGen
