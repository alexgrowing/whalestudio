import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LogGapMeasurableScaleStable
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_gap_measurable_scale_stable : ∀ (n : ℕ) (h : HermNorm n) (u : Fin n → ℂ),
  Measurable (logGap h u) ∧ ∀ s : ℝ≥0∞, IsOpen {y | s < logGap h u y} ∧ IsScaleStable {y | s < logGap h u y} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic <;> assumption)
