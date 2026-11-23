import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteInvarianceFirstOfPublished
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_invariance_first_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.InfInvA := by
  first | exact @GlobalTheory.ThK.LemF.infInvA_holds | exact GlobalTheory.ThK.LemF.infInvA_holds | (intros; apply GlobalTheory.ThK.LemF.infInvA_holds <;> assumption)
