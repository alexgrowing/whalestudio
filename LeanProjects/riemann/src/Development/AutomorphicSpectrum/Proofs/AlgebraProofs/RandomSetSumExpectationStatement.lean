import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RandomSetSumExpectation
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.random_set_sum_expectation : ∀ {Ω Y : Type} [MeasurableSpace Ω] [MeasurableSpace Y] (P : Measure Ω) (ν : Measure Y)
  (L : Ω → Set Y) (φ : Y → ℝ≥0∞) (c : ℝ≥0∞), Measurable φ →
  (∀ s : ℝ≥0∞, Measurable fun ω => (((L ω ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞)) →
  (∀ s : ℝ≥0∞, ∫⁻ ω, (((L ω ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞) ∂P = c * ν {y | s < φ y}) →
    Measurable (fun ω => ∑' y : L ω, φ y) ∧ ∫⁻ ω, ∑' y : L ω, φ y ∂P = c * ∫⁻ y, φ y ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake.measurable_lintegral_tsum_of_level_counts | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake.measurable_lintegral_tsum_of_level_counts | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake.measurable_lintegral_tsum_of_level_counts <;> assumption)
