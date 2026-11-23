import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricTranslationPullbackFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationPreservesFlatFormStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_translation_pullback_flat : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ), IsMetric B τ M j h → ChernIsFlat B τ h → ∀ x : Fl g, IsMetric B τ M (translPullFactor τ x j) (fun P => h (transl τ x P)) ∧ ChernIsFlat B τ (fun P => h (transl τ x P)) := by
  first | exact @GlobalTheory.FlatTransl.translate_isMetric_chernIsFlat | exact GlobalTheory.FlatTransl.translate_isMetric_chernIsFlat | (intros; apply GlobalTheory.FlatTransl.translate_isMetric_chernIsFlat <;> assumption)
