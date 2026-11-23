import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierSuperposition
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

theorem exists_rapid_superposition_characters :
    ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (Φ : Z → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (κ : X → ℂ) (τ : X → Z →L[ℝ] ℝ), Measurable κ ∧ (∀ z, Measurable fun x => τ x z) ∧ (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) ∧ ∀ z, Φ z = ∫ x, κ x * (𝐞 (τ x z) : ℂ) ∂ν := by
  intro Z _ _ _ Φ hΦ hc
  obtain ⟨m, A, φ, hφ, hint, hinv⟩ := GlobalTheory.fourier_inversion_real_linear_forms (hc.toSchwartzMap hΦ)
  let B : EuclideanSpace ℝ (Fin m) →L[ℝ] (Z →L[ℝ] ℝ) := (2 * Real.pi)⁻¹ • A
  have hB : ∀ w z, 2 * Real.pi * B w z = A w z := by
    intro w z
    have : (2 * Real.pi) ≠ 0 := by positivity
    simp only [B, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  refine ⟨EuclideanSpace ℝ (Fin m), inferInstance, volume, inferInstance, φ, fun w => B w,
    hφ.measurable, fun z => ?_, fun N => ?_, fun z => ?_⟩
  · exact (by fun_prop : Continuous fun x => B x z).measurable
  · refine ((hint N).const_mul ((1 + ‖B‖) ^ N)).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact (by fun_prop : Continuous fun x => ‖φ x‖ * (1 + ‖B x‖) ^ N).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc, ← mul_pow, mul_comm]
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ N) (norm_nonneg _)
      have h1 := B.le_opNorm w
      nlinarith [norm_nonneg B, norm_nonneg w]
  · have h := hinv z
    have h0 : (hc.toSchwartzMap hΦ) z = Φ z := rfl
    rw [h0] at h
    rw [h]
    congr 1
    ext w
    rw [Real.fourierChar_apply, hB]

end GlobalTheory.JSW
