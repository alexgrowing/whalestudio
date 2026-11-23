import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalMetricLocalToGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricDeterminedByCurvatureZeroSectionStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_metric_local_to_global : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (r : E → ℂ), (∀ b₀ ∈ B, ∃ U : Set E, IsOpen U ∧ b₀ ∈ U ∧ U ⊆ B ∧ ∃ h, IsCubicalMetric U τ j r h) → ∃ h, IsCubicalMetric B τ j r h := by
  first | exact @GlobalTheory.cubicalMetric_exists_of_local | exact GlobalTheory.cubicalMetric_exists_of_local | (intros; apply GlobalTheory.cubicalMetric_exists_of_local <;> assumption)
