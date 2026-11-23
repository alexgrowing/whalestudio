import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicParamIntegral
import Mathlib
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_param_integral : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (θ : β → α → ℂ) (H : ℂ → α → ℂ) (s₀ : ℂ) (r M : ℝ),
    (∀ s ∈ Metric.ball s₀ r, AEStronglyMeasurable (fun p : β × α => θ p.1 p.2 * H s p.2) (ν.prod μ)) →
    (∀ a, DifferentiableOn ℂ (fun s => H s a) (Metric.ball s₀ r)) →
    (∀ s ∈ Metric.ball s₀ r, ∀ b a, ‖θ b a * H s a‖ ≤ M) →
    DifferentiableOn ℂ (fun s => ∫ b, ∫ a, θ b a * H s a ∂μ ∂ν) (Metric.ball s₀ r) := by
  first | exact @GlobalTheory.differentiableOn_double_integral_of_bounded_holomorphic | exact GlobalTheory.differentiableOn_double_integral_of_bounded_holomorphic | (intros; apply GlobalTheory.differentiableOn_double_integral_of_bounded_holomorphic <;> assumption)
