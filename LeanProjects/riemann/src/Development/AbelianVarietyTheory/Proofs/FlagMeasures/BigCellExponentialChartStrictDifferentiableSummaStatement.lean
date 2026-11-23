import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellExponentialChartStrictDifferentiableSumma
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCellExponentialChart_strictDifferentiable_summary : ∀ (k r : ℕ), chart k r 0 = 1 ∧ ContinuousOn (chart k r) (Metric.ball 0 1) ∧ ∀ i j, ∃ D : EE k r →L[ℝ] ℂ, HasStrictFDerivAt (fun v => chart k r v i j) D 0 ∧ ∀ v, D v = dchart k r v i j := by
  first | exact @GlobalTheory.CellDens.Deriv.chart_strict | exact GlobalTheory.CellDens.Deriv.chart_strict | (intros; apply GlobalTheory.CellDens.Deriv.chart_strict <;> assumption)
