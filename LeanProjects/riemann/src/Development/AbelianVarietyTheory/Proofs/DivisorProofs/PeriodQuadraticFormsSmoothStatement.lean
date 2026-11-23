import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodQuadraticFormsSmooth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReQuad
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.ThetaMet
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_quadratic_forms_smooth : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ContDiffOn ℝ ∞ (flat τ) (cov B g) ∧ ContDiffOn ℝ ∞ (quad τ) (cov B g) ∧ ContDiffOn ℝ ∞ (reQuad τ) (cov B g) := by
  first | exact @GlobalTheory.ThetaMetSmooth.smooth_main | exact GlobalTheory.ThetaMetSmooth.smooth_main | (intros; apply GlobalTheory.ThetaMetSmooth.smooth_main <;> assumption)
