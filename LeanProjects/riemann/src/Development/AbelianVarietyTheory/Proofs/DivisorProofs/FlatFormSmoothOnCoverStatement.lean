import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormSmoothOnCover
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_form_smooth_on_cover : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ContDiffOn ℝ ∞ (om0 τ) (cov B g) := by
  first | exact @GlobalTheory.FlatSmooth.main | exact GlobalTheory.FlatSmooth.main | (intros; apply GlobalTheory.FlatSmooth.main <;> assumption)
