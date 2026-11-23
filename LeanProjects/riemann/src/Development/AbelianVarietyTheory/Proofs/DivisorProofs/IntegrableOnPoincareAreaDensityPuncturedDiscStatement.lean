import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnPoincareAreaDensityPuncturedDisc
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_poincareAreaDensity_punctured_disc : IntegrableOn (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2) (Metric.closedBall 0 (1 / 2)) := by
  first | exact @GlobalTheory.GoodTop.integrableOn_poincare_disc | exact GlobalTheory.GoodTop.integrableOn_poincare_disc | (intros; apply GlobalTheory.GoodTop.integrableOn_poincare_disc <;> assumption)
