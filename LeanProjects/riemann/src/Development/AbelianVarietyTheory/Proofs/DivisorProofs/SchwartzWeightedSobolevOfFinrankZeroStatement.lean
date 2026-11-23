import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzWeightedSobolevOfFinrankZero
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_weighted_sobolev_bound_of_finrank_eq_zero : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], finrank ℝ E = 0 → ∀ (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by
  first | exact @GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero | exact GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero | (intros; apply GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero <;> assumption)
