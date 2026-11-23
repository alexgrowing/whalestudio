import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodFlatMapRealAnalytic
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_flat_map_real_analytic : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → AnalyticOnNhd ℝ (flat τ) (cov B g) ∧ AnalyticOnNhd ℝ (fun Q : E × Fl g => per (τ Q.1) Q.2) (B ×ˢ Set.univ) := by
  first | exact @GlobalTheory.FlatAnalytic.flat_analytic | exact GlobalTheory.FlatAnalytic.flat_analytic | (intros; apply GlobalTheory.FlatAnalytic.flat_analytic <;> assumption)
