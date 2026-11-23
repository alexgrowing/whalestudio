import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSqHolomorphicPluriharmonic
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_sq_holomorphic_pluriharmonic : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {s : Set (Pt E g)} {φ : Pt E g → ℂ}, IsOpen s → DifferentiableOn ℂ φ s → (∀ P ∈ s, φ P ≠ 0) → ∀ P ∈ s, ∀ v w : Pt E g, ddc (fun Q => Real.log (‖φ Q‖ ^ 2)) P v w = 0 := by
  first | exact @GlobalTheory.ddc_log_normSq_eq_zero | exact GlobalTheory.ddc_log_normSq_eq_zero | (intros; apply GlobalTheory.ddc_log_normSq_eq_zero <;> assumption)
