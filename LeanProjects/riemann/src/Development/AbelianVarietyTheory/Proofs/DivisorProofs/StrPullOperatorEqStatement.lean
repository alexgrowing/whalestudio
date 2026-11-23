import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrPullOperatorEq
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.str_pull_operator_eq : ∀ {n g : ℕ} (a : Fin n → ℂ) (K : Ext (n + n + g) →L[ℂ] Ext (n + n + g)), strN (pullOp a K) = pullBaseL a (strN K) := by
  first | exact @GlobalTheory.TorsionForm.OneVec.strN_pullOp | exact GlobalTheory.TorsionForm.OneVec.strN_pullOp | (intros; apply GlobalTheory.TorsionForm.OneVec.strN_pullOp <;> assumption)
