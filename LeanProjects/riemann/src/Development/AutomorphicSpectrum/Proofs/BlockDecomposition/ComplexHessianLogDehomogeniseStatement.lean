import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogDehomogenise
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_hessian_log_dehomogenise : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → ∀ z ∈ U, cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z = cHess d (fun v => ((Real.log (1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2) : ℝ) : ℂ)) z := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq | exact GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq <;> assumption)
