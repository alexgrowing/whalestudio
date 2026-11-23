import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GradedSeriesContinuationDominated

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_and_summable_on_ball_of_hasSum_on_interval : ∀ {ι : Type} (deg : ι → ℕ), (∀ k, {i | deg i = k}.Finite) → ∀ (a : ι → ℂ) (b : ι → ℝ) (C δ ρ : ℝ) (P P' : ℂ → ℂ), 0 < δ → (∀ i, 0 ≤ b i) → (∀ i, ‖a i‖ ≤ C * b i) → DifferentiableOn ℂ P (Metric.ball 0 ρ) → DifferentiableOn ℂ P' (Metric.ball 0 ρ) → (∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => a i * (x : ℂ) ^ deg i) (P x) ∧ HasSum (fun i => (b i : ℂ) * (x : ℂ) ^ deg i) (P' x)) → ∀ X : ℂ, ‖X‖ < ρ → HasSum (fun i => a i * X ^ deg i) (P X) ∧ Summable (fun i => b i * ‖X‖ ^ deg i) := by
  first | exact @GlobalTheory.gradedSeries_continuation_dominated | exact GlobalTheory.gradedSeries_continuation_dominated | (intros; apply GlobalTheory.gradedSeries_continuation_dominated <;> assumption)
