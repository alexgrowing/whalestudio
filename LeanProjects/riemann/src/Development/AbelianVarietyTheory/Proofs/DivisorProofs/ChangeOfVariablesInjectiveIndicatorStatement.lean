import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChangeOfVariablesInjectiveIndicator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.change_of_variables_injective_indicator : ∀ (d : ℕ) (g h : (Fin d → ℂ) → Fin d → ℂ) (g' : (Fin d → ℂ) → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)) (s : Set (Fin d → ℂ)) (F φ K : (Fin d → ℂ) → ℝ), MeasurableSet s → (∀ x ∈ s, HasFDerivWithinAt g (g' x) s x) → Set.InjOn g s → (∀ x ∈ s, h (g x) = x) → (∀ x ∈ s, (g' x).det ≠ 0) → (∀ x, x ∉ s → F x = 0) → K = (g '' s).indicator (fun w => F (h w) * |(g' (h w)).det|⁻¹) → ∫ x, φ (g x) * F x = ∫ w, φ w * K w := by
  first | exact @GlobalTheory.integral_comp_mul_eq_integral_mul_indicator_jacobian | exact GlobalTheory.integral_comp_mul_eq_integral_mul_indicator_jacobian | (intros; apply GlobalTheory.integral_comp_mul_eq_integral_mul_indicator_jacobian <;> assumption)
