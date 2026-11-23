import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormNormsMinorsEqLabelProof
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label : GlobalTheory.TypeAsm.LabC := by
  first | exact @GlobalTheory.TypeAsm.labC | exact GlobalTheory.TypeAsm.labC | (intros; apply GlobalTheory.TypeAsm.labC <;> assumption)
