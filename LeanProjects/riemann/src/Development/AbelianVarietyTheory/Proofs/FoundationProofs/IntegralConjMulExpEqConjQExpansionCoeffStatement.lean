import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjMulExpEqConjQExpansionCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_conj_mul_exp_eq_conj_qExpansion_coeff : ∀ (h : ℍ → ℂ) (T : ℝ) (n : ℕ) (y : ℝ), 0 < T → 0 < y → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → Function.Periodic (h ∘ ofComplex) T → IsBoundedAtImInfty h → (∫ x in (0 : ℝ)..T, (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) = T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral | exact GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral | (intros; apply GlobalTheory.HeckeFamilyMatrices.Qc.conj_integral <;> assumption)
