import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormIntegralStarMulSqLeMul
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_integral_star_mul_sq_le_mul : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (f h : X → ℂ), AEStronglyMeasurable f μ → AEStronglyMeasurable h μ → Integrable (fun x => star (f x) * f x) μ → Integrable (fun x => star (h x) * h x) μ → ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ (∫ x, star (f x) * f x ∂μ).re * (∫ x, star (h x) * h x ∂μ).re := by
  first | exact @GlobalTheory.norm_integral_star_mul_sq_le | exact GlobalTheory.norm_integral_star_mul_sq_le | (intros; apply GlobalTheory.norm_integral_star_mul_sq_le <;> assumption)
