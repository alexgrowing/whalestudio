import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalInvarianceSecondOfHyp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eval_invariance_second_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.EvInvB := by
  first | exact @GlobalTheory.ThK.LemF.evInvB_of_hypotheses | exact GlobalTheory.ThK.LemF.evInvB_of_hypotheses | (intros; apply GlobalTheory.ThK.LemF.evInvB_of_hypotheses <;> assumption)
