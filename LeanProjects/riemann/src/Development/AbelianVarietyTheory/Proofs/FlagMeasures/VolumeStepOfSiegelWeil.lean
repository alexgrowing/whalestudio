import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EnnrealVolumeRatioStepCancel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoTsumOfMonotone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMeanCcOfOneVectorCc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil

open GlobalTheory.FlagMeas GlobalTheory.GaussMean

namespace GlobalTheory.GaussMean

theorem volumeStep_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → VolumeStep := fun h =>
  GlobalTheory.GaussMean.Step.volumeStep_of_siegelMean
    (GlobalTheory.GaussMean.Limit.siegelMean_of_cc
      (GlobalTheory.OneVectorMean.siegelMeanCc_of_oneVectorCc
        (GlobalTheory.GaussMean.oneVectorCc_of_siegelWeil h)))

end GlobalTheory.GaussMean
