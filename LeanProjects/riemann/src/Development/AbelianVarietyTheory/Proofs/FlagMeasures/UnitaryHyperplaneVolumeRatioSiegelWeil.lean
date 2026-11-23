import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeRatio
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelOneVectorMeasurableOfCompactSupportStatement

namespace GlobalTheory.VolRatioFromSiegelWeil

theorem volumeRatio :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.RT.MassRatioUnderVolume D :=
  fun hP =>
    GlobalTheory.VolRatioFromSecondClause.volumeRatio
      (GlobalTheory.T.siegel_one_vector_measurable_of_compactSupport (GlobalTheory.GaussMean.oneVectorCc_of_siegelWeil hP))

end GlobalTheory.VolRatioFromSiegelWeil
