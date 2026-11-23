import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.HidaX
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HdEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsHeckeIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckePolyCoeffZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaLevelX

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Th UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
theorem UpperTheory.V.Th.hida_x_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.HidaFamilyCondition := by
  intro P l _ L Ω _ _ _ _ _ _ s V hS c n hn r B Λ ι
  obtain ⟨R⟩ := _root_.UpperTheory.V.Hi.nonempty_unitaryHeckeData P l L Ω s n hn V (QData.empty V hS) c r ι Λ
  let K : (hset (QData.empty V hS) R.τ₀).Lev := ⟨fun q => Empty.elim q, fun q => Empty.elim q⟩
  obtain ⟨J, hJ⟩ := _root_.UpperTheory.V.Hi.exists_hecke_ideal P l L Ω s n hn V _ c r ι B Λ R K
  exact ⟨J, _root_.UpperTheory.V.Hi.hecke_ideal_point_properties P l L Ω s n hn V _ c r ι B Λ R K hS J hJ, _root_.UpperTheory.V.Th.AnnihilatorQuotientFinite.levelX_of_isJ_unitaryHeckeData P l L Ω s n hn V _ c r ι B Λ R K hS J hJ⟩
end
