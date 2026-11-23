import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TailLogIntegralBoundOfDistribution
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tail_log_integral_bound_of_distribution : ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X) (r : X → ℝ) (D : ℕ) (C R : ℝ), Measurable r → 0 ≤ C → Real.exp 1 ≤ R → (∀ ρ, R ≤ ρ → μ {x | ρ ≤ r x} ≤ ENNReal.ofReal (C * Real.log ρ ^ D / ρ)) → ∫⁻ x in {x | R ≤ r x}, ENNReal.ofReal (Real.log (r x)) ∂μ ≤ ENNReal.ofReal (C * (∑' k : ℕ, ((k : ℝ) + 2) ^ (D + 1) / 2 ^ k) * Real.log R ^ (D + 1) / R) := by
  first | exact @GlobalTheory.lintegral_log_le_of_tail_bound | exact GlobalTheory.lintegral_log_le_of_tail_bound | (intros; apply GlobalTheory.lintegral_log_le_of_tail_bound <;> assumption)
