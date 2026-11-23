import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteInvarianceSecondOfPublished
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_invariance_second_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.InfInvB := by
  first | exact @GlobalTheory.ThK.InfB.infInvB_of_hypotheses | exact GlobalTheory.ThK.InfB.infInvB_of_hypotheses | (intros; apply GlobalTheory.ThK.InfB.infInvB_of_hypotheses <;> assumption)
