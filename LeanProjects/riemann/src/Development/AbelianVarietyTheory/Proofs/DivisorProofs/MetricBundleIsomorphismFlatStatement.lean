import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricBundleIsomorphismFlat
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_bundle_isomorphism_flat : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (M : Submodule ℤ (Fl g)) (j j' : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ) (φ : Pt E g → ℂ), IsMetric B τ M j h → ChernIsFlat B τ h → IsBundleIso B τ M j j' φ → IsMetric B τ M j' (fun P => h P / ‖φ P‖ ^ 2) ∧ ChernIsFlat B τ (fun P => h P / ‖φ P‖ ^ 2) := by
  first | exact @GlobalTheory.BundleIsoMetric.div_normSq_isMetric_chernIsFlat | exact GlobalTheory.BundleIsoMetric.div_normSq_isMetric_chernIsFlat | (intros; apply GlobalTheory.BundleIsoMetric.div_normSq_isMetric_chernIsFlat <;> assumption)
