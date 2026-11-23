import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnInvMulLogSqNearZero
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_inv_mul_log_sq_near_zero : IntegrableOn (fun t : ℝ => t * (t * |Real.log t|)⁻¹ ^ 2) (Set.Ioc 0 (1 / 2)) := by
  first | exact @GlobalTheory.GoodTop.integrableOn_inv_mul_log_sq | exact GlobalTheory.GoodTop.integrableOn_inv_mul_log_sq | (intros; apply GlobalTheory.GoodTop.integrableOn_inv_mul_log_sq <;> assumption)
