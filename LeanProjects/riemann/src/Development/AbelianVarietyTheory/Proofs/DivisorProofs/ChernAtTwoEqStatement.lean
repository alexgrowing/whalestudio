import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernAtTwoEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernAt_two_eq_ofValuesTwo_chernTwo : ∀ {n : ℕ} (G : V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (v : V n), chernAt G v 2 = ofValuesTwo (chernTwo G v) := by
  first | exact @GlobalTheory.SecForm.chernAt_two_eq | exact GlobalTheory.SecForm.chernAt_two_eq | (intros; apply GlobalTheory.SecForm.chernAt_two_eq <;> assumption)
