import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermAbsoluteVolumeBoundOfVolumeRatioInduction
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermAbsoluteVolumeBound_of_volume_ratio_induction : VolumeStep → AbsoluteVolume := by
  first | exact @GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep | exact GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep | (intros; apply GlobalTheory.FlagMeas.AbsVol.absoluteVolume_of_volumeStep <;> assumption)
