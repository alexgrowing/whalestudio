import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromITailExponentialDecay
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerIntegralFromI_tail_exponential_decay : ∀ (w : ℕ) (F : ℍ → ℂ) (C c : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → 0 < c → (∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-c * τ.im)) → ∃ (L : ℂ[X]) (C' : ℝ), ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(eichler w F τ - L).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.eichler_tail | exact GlobalTheory.HeckeFamilyMatrices.eichler_tail | (intros; apply GlobalTheory.HeckeFamilyMatrices.eichler_tail <;> assumption)
