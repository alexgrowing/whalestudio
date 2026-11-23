import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in

theorem _root_.GlobalTheory.GoodTop.continuousAt_mixTop :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
      {K : _root_.ReciprocityTheory.L2DbarEstimates.V n → Fin n → _root_.GlobalTheory.GoodTop.EndValuedForm11Coeffs n r} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n},
      (∀ i a b p q, ContinuousAt (fun x => K x i a b p q) v) →
        ContinuousAt (fun x => _root_.GlobalTheory.GoodTop.mixTop (K x)) v := by
  intro n r _ _ K v hK
  unfold _root_.GlobalTheory.GoodTop.mixTop
  simp only [Matrix.det_apply, Matrix.of_apply]
  fun_prop

end GlobalTheory.GoodTop
