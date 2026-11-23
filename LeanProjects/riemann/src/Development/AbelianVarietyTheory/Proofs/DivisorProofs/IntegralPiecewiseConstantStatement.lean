import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPiecewiseConstant
import Mathlib
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_piecewise_constant : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) {ι : Type} [Countable ι] (S : ι → Set X),
    (∀ k, MeasurableSet (S k)) → Pairwise (Function.onFun Disjoint S) → (∀ x, ∃ k, x ∈ S k) → (∀ k, μ (S k) = 1) →
    ∀ (g : ι → ℂ), Summable (fun k => ‖g k‖) → ∀ f : X → ℂ, (∀ k, ∀ x ∈ S k, f x = g k) →
    ∫ x, f x ∂μ = ∑' k, g k := by
  first | exact @GlobalTheory.integral_eq_tsum_of_const_on_partition_measure_one | exact GlobalTheory.integral_eq_tsum_of_const_on_partition_measure_one | (intros; apply GlobalTheory.integral_eq_tsum_of_const_on_partition_measure_one <;> assumption)
