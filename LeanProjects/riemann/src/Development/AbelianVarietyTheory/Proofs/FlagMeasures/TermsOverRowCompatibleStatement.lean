import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOverRowCompatible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termsOverRow_compatible : GlobalTheory.TypeAsm.CompatC := by
  first | exact @GlobalTheory.TypeAsm.CompatPf.compatC | exact GlobalTheory.TypeAsm.CompatPf.compatC | (intros; apply GlobalTheory.TypeAsm.CompatPf.compatC <;> assumption)
