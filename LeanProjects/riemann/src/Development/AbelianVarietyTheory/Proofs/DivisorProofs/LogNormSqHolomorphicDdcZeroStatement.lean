import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSqHolomorphicDdcZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_sq_holomorphic_ddc_zero : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (U : Set (Pt E g)) (φ : Pt E g → ℂ), IsOpen U → DifferentiableOn ℂ φ U → (∀ P ∈ U, φ P ≠ 0) → ∀ P ∈ U, ∀ v w : Pt E g, ddc (fun Q => Real.log (‖φ Q‖ ^ 2)) P v w = 0 := by
  first | exact @GlobalTheory.LogNormPluriharm.ddc_log_norm_sq_eq_zero | exact GlobalTheory.LogNormPluriharm.ddc_log_norm_sq_eq_zero | (intros; apply GlobalTheory.LogNormPluriharm.ddc_log_norm_sq_eq_zero <;> assumption)
