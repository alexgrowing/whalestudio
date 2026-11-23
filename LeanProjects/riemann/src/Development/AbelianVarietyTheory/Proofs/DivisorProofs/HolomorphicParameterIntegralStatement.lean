import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicParameterIntegral
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_parameter_integral : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μK : Measure α) [IsFiniteMeasure μK] (μ : Measure β) [SFinite μ]
    (A : α → β → ℂ) (a : β → ℝ), Measurable a → (∀ l, 0 < a l) → AEStronglyMeasurable (Function.uncurry A) (μK.prod μ) →
    ∀ g : β → ℝ, (∀ s : ℝ, 1 < s → Integrable (fun l => g l * a l ^ s) μ) → (∀ k l, ‖A k l‖ ≤ g l) →
    DifferentiableOn ℂ (fun z : ℂ => ∫ k, ∫ l, A k l * ((a l : ℝ) : ℂ) ^ z ∂μ ∂μK) {z : ℂ | 1 < z.re} := by
  first | exact @GlobalTheory.differentiableOn_integral_integral_mul_cpow | exact GlobalTheory.differentiableOn_integral_integral_mul_cpow | (intros; apply GlobalTheory.differentiableOn_integral_integral_mul_cpow <;> assumption)
