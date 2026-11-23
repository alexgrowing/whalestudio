import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeInvarianceFirstOfHyp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_invariance_first_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.ConeInvA := by
  first | exact @GlobalTheory.ThK.LemF.coneInvA | exact GlobalTheory.ThK.LemF.coneInvA | (intros; apply GlobalTheory.ThK.LemF.coneInvA <;> assumption)
