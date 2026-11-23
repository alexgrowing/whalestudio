import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumFourierSeriesOfExpDecay
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegL1Norm
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TauPeriod Complex
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_fourier_series_of_exp_decay : ∀ {g : ℕ} (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (j : Fin g) z, f (z + Pi.single j 1) = f z) → (∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, ∀ n : Fin g → ℤ, ‖cf f n‖ ≤ M * Real.exp (-(2 * π * R) * l1 n)) → ∀ z : Fin g → ℂ, HasSum (fun n : Fin g → ℤ => cf f n * ex n z) (f z) := by
  first | exact @GlobalTheory.TauPeriod.hasSum_cf_mul_ex | exact GlobalTheory.TauPeriod.hasSum_cf_mul_ex | (intros; apply GlobalTheory.TauPeriod.hasSum_cf_mul_ex <;> assumption)
