import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalH
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthMix
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVRPropMV
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.Esk
theorem mixSeed_of_holWC_alt (w : HolWC) (P : _root_.UpperTheory.V.Af.HypothesesH') (h : UpperTheory.V.Sd.PropMHol) : _root_.UpperTheory.V.Z.Win.Birth.MixSeedP :=
  _root_.UpperTheory.V.Z.Win.Birth.mix_birth_of_prints P (_root_.UpperTheory.Esk.pf_PropMV_sv_alt P h w (_root_.UpperTheory.Esk.pf_HRep_alt P s_HCap))
end UpperTheory.Esk
end
