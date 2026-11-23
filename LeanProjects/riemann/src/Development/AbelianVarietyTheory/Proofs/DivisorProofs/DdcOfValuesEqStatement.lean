import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcOfValuesEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_ofValues_eq : ∀ {n : ℕ} (α : V n → V n → V n → ℂ) (v : V n), (∀ a b, ContDiffAt ℝ 2 (fun x => α x (coordVec a) (coordVec b)) v) → kappa • delAt (dbarAt fun x => (ofValues (α x) : Alt n)) v = (ofValuesTwo (ddcForm α v) : Alt n) := by
  first | exact @GlobalTheory.SecForm.ddc_ofValues | exact GlobalTheory.SecForm.ddc_ofValues | (intros; apply GlobalTheory.SecForm.ddc_ofValues <;> assumption)
