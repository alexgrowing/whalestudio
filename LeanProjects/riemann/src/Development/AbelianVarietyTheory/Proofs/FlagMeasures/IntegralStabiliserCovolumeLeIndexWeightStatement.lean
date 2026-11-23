import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserCovolumeLeIndexWeight
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralStabiliser_covolume_le_indexWeight : GlobalTheory.TypeAsm.CovTC := by
  first | exact @GlobalTheory.TypeAsm.covTC_holds | exact GlobalTheory.TypeAsm.covTC_holds | (intros; apply GlobalTheory.TypeAsm.covTC_holds <;> assumption)
