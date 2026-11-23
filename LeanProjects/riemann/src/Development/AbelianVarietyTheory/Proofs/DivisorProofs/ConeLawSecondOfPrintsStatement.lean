import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeLawSecondOfHyp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_law_second_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.ConeLawB := by
  first | exact @GlobalTheory.ThK.LemF.coneLawB | exact GlobalTheory.ThK.LemF.coneLawB | (intros; apply GlobalTheory.ThK.LemF.coneLawB <;> assumption)
