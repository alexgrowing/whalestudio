import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermVolumeRatioSameKindOfVolumeRatioInduction
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermVolumeRatioSameKind_of_volumeRatioInduction : VolumeStep → VolumeRatio := by
  first | exact @GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep | exact GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep | (intros; apply GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep <;> assumption)
