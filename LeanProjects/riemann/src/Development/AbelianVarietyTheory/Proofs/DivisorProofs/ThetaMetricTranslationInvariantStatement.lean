import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMetricTranslationInvariant
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_metric_translation_invariant : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (x : Fl g), ∀ P ∈ cov B g, Real.exp (-2 * π * ((fun i => ((transl τ x P).2 i).im) ⬝ᵥ ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => ((transl τ x P).2 i).im))) * ‖Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) x P.2)‖ ^ 2 = Real.exp (-2 * π * ((fun i => (P.2 i).im) ⬝ᵥ ((((τ P.1).map Complex.im)⁻¹) *ᵥ fun i => (P.2 i).im))) := by
  first | exact @GlobalTheory.thetaMetric_transl_invariant | exact GlobalTheory.thetaMetric_transl_invariant | (intros; apply GlobalTheory.thetaMetric_transl_invariant <;> assumption)
