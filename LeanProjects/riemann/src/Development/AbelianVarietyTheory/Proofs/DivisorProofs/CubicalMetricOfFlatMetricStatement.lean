import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalMetricOfFlatMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormMulPullZeroSectionStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_metric_of_flat_metric : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ) (r : E → ℂ), IsMetric B τ (stdLat g) j h → ChernIsFlat B τ h → IsRigidification B r → IsCubicalMetric B τ j r (fun P => h P / (h (zeroSec g P.1) * ‖r P.1‖ ^ 2)) := by
  first | exact @GlobalTheory.NormCubical.normalise_cubical | exact GlobalTheory.NormCubical.normalise_cubical | (intros; apply GlobalTheory.NormCubical.normalise_cubical <;> assumption)
