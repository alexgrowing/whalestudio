import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtIntegralDominatedFamily
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.has_deriv_at_integral_dominated_family : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F F₁ F₂ : ℝ → α → ℂ) (B : ℝ),
    (∀ x s, HasDerivAt (fun r => F r x) (F₁ s x) s) → (∀ x s, HasDerivAt (fun r => F₁ r x) (F₂ s x) s) →
    (∀ s, Integrable (F s) μ) → (∀ s, Integrable (F₁ s) μ) → (∀ s, Integrable (F₂ s) μ) →
    (∀ s ∈ Set.Icc (-1 : ℝ) 1, ∫ x, ‖F₁ s x‖ ∂μ ≤ B) → (∀ s ∈ Set.Icc (-1 : ℝ) 1, ∫ x, ‖F₂ s x‖ ∂μ ≤ B) →
    HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, F₁ 0 x ∂μ) 0 := by
  first | exact @GlobalTheory.hasDerivAt_integral_of_integral_bounds | exact GlobalTheory.hasDerivAt_integral_of_integral_bounds | (intros; apply GlobalTheory.hasDerivAt_integral_of_integral_bounds <;> assumption)
