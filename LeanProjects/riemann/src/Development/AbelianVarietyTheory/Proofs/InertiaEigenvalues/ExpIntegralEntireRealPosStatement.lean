import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPos
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_integral_differentiable_real_re_pos : ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) (f t : X → ℝ), Measurable f → Measurable t → (∀ y, 0 ≤ f y) →
    Integrable f ν → (∃ R : ℝ, ∀ y, f y ≠ 0 → |t y| ≤ R) →
    Differentiable ℂ (fun s : ℂ => ∫ y, (f y : ℂ) * Complex.exp (s * t y) ∂ν) ∧
    ∀ r : ℝ, (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).im = 0 ∧
      (0 < ∫ y, f y ∂ν → 0 < (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).re) := by
  first | exact @GlobalTheory.exp_integral_entire_real_pos | exact GlobalTheory.exp_integral_entire_real_pos | (intros; apply GlobalTheory.exp_integral_entire_real_pos <;> assumption)
