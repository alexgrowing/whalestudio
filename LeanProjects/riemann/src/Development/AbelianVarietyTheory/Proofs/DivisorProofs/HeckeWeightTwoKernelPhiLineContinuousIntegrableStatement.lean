import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoKernelPhiLineContinuousIntegrable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwoKernelPhi_line_continuous_integrable : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧ MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  first | exact @GlobalTheory.HeckeTwo.phi_line_continuous_integrable | exact GlobalTheory.HeckeTwo.phi_line_continuous_integrable | (intros; apply GlobalTheory.HeckeTwo.phi_line_continuous_integrable <;> assumption)
