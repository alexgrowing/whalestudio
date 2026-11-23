import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnSummableFourierSeries
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegL1Norm
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TauPeriod Complex
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_summable_fourier_series : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {V : Set E} (d : (Fin g → ℤ) → E → ℂ), IsOpen V → (∀ n, DifferentiableOn ℂ (d n) V) → (∀ K ⊆ V, IsCompact K → ∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, ∀ n, ∀ b ∈ K, ‖d n b‖ ≤ M * Real.exp (-(2 * π * R) * l1 n)) → DifferentiableOn ℂ (fun P : Pt E g => ∑' n, d n P.1 * ex n P.2) (cov V g) ∧ ∀ P : Pt E g, P.1 ∈ V → Summable (fun n => d n P.1 * ex n P.2) := by
  first | exact @GlobalTheory.TauPeriod.differentiableOn_tsum_coeff_mul_ex | exact GlobalTheory.TauPeriod.differentiableOn_tsum_coeff_mul_ex | (intros; apply GlobalTheory.TauPeriod.differentiableOn_tsum_coeff_mul_ex <;> assumption)
