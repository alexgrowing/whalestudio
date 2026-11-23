import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in

theorem _root_.GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen {n : ℕ} (S : Finset (Fin n)) (U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (hU : IsOpen U) :
    IsOpen (_root_.GlobalTheory.GoodTop.offHyp S U) := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  have hset : {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0} =
      U ∩ ⋂ a ∈ S, {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a ≠ 0} := by
    ext v
    simp
  rw [hset]
  refine hU.inter (isOpen_biInter_finset fun a _ => isOpen_ne_fun ?_ continuous_const)
  unfold _root_.ReciprocityTheory.L2DbarEstimates.V
  fun_prop

end GlobalTheory.GoodTop
