import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralZero
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTopFormChartIntegral_zero : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] (e : κ → OpenPartialHomeomorph Y (V n)) (S : Set Y), HasInt e (fun _ _ => 0) S 0 := by
  first | exact @GlobalTheory.GoodTop.hasInt_zero | exact GlobalTheory.GoodTop.hasInt_zero | (intros; apply GlobalTheory.GoodTop.hasInt_zero <;> assumption)
