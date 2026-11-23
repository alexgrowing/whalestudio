import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOffCoordinateHyperplanes
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_offCoordinateHyperplanes : ∀ {n : ℕ} (S : Finset (Fin n)) (U : Set (V n)), IsOpen U → IsOpen (offHyp S U) := by
  first | exact @GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen | exact GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen | (intros; apply GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen <;> assumption)
