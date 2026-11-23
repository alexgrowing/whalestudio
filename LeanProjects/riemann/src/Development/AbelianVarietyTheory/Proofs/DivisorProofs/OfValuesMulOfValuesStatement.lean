import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfValuesMulOfValues
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ofValues_mul_ofValues' : ∀ {n : ℕ} (α β : V n → V n → ℂ), ofValues α * ofValues β = ofValuesTwo (wedge α β) := by
  first | exact @GlobalTheory.SecForm.ofValues_mul_ofValues | exact GlobalTheory.SecForm.ofValues_mul_ofValues | (intros; apply GlobalTheory.SecForm.ofValues_mul_ofValues <;> assumption)
