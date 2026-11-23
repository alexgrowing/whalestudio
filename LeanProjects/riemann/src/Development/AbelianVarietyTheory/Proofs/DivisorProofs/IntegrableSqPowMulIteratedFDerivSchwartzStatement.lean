import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableSqPowMulIteratedFDerivSchwartz
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_sq_norm_pow_mul_iteratedFDeriv_schwartz : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (i j : ℕ), Integrable (fun z => (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2) μ := by
  first | exact @GlobalTheory.integrable_sq_pow_mul_iteratedFDeriv_schwartz | exact GlobalTheory.integrable_sq_pow_mul_iteratedFDeriv_schwartz | (intros; apply GlobalTheory.integrable_sq_pow_mul_iteratedFDeriv_schwartz <;> assumption)
