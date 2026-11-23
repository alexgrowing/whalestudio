import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeLawFirstOfHyp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_law_first_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.ConeLawA := by
  first | exact @GlobalTheory.ThK.LemF.coneLawA | exact GlobalTheory.ThK.LemF.coneLawA | (intros; apply GlobalTheory.ThK.LemF.coneLawA <;> assumption)
