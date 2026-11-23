import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPolarisedTopChernCoeff
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_polarisedTopChernCoeff : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {K : V n → Fin n → EndValuedForm11Coeffs n r} {v : V n}, (∀ i a b p q, ContinuousAt (fun x => K x i a b p q) v) → ContinuousAt (fun x => mixTop (K x)) v := by
  first | exact @GlobalTheory.GoodTop.continuousAt_mixTop | exact GlobalTheory.GoodTop.continuousAt_mixTop | (intros; apply GlobalTheory.GoodTop.continuousAt_mixTop <;> assumption)
