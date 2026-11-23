import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnLaplaceIntegralRightHalf
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_laplace_integral_right_half : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (G : X → ℂ) (L : X → ℝ), AEStronglyMeasurable G μ → Measurable L → (∀ σ : ℝ, 0 < σ → Integrable (fun x => ‖G x‖ * Real.exp (σ * L x)) μ) → DifferentiableOn ℂ (fun u : ℂ => ∫ x, G x * Complex.exp (u * (L x : ℂ)) ∂μ) {u : ℂ | 0 < u.re} := by
  first | exact @GlobalTheory.CompanionTheory.HoloFamily.differentiableOn_integral_mul_cexp | exact GlobalTheory.CompanionTheory.HoloFamily.differentiableOn_integral_mul_cexp | (intros; apply GlobalTheory.CompanionTheory.HoloFamily.differentiableOn_integral_mul_cexp <;> assumption)
