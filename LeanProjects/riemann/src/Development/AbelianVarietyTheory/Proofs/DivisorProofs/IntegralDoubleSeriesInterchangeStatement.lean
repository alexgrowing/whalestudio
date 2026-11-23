import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDoubleSeriesInterchange
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_double_series_interchange : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (𝓕 : Set X), μ 𝓕 ≠ ⊤ → ∀ (ι κ : Type) [Countable ι] [Countable κ]
    (Φ : ι → κ → X → ℂ), (∀ i k, Measurable (Φ i k)) → ∀ C : ℝ,
    (∀ u, Summable (fun p : ι × κ => ‖Φ p.1 p.2 u‖) ∧ ∑' p : ι × κ, ‖Φ p.1 p.2 u‖ ≤ C) →
    (∫ u in 𝓕, ∑' p : ι × κ, Φ p.1 p.2 u ∂μ = ∑' i, ∫ u in 𝓕, ∑' k, Φ i k u ∂μ) ∧
      Summable (fun i => ‖∫ u in 𝓕, ∑' k, Φ i k u ∂μ‖) := by
  first | exact @GlobalTheory.integral_tsum_prod_of_bounded | exact GlobalTheory.integral_tsum_prod_of_bounded | (intros; apply GlobalTheory.integral_tsum_prod_of_bounded <;> assumption)
