import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorMulOfPublished
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_operator_mul_of_classicalTheorems : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.LocOpMul := by
  first | exact @GlobalTheory.ThK.LemF.locOpMul | exact GlobalTheory.ThK.LemF.locOpMul | (intros; apply GlobalTheory.ThK.LemF.locOpMul <;> assumption)
