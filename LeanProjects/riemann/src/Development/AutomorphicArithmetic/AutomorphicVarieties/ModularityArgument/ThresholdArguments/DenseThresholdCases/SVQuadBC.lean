import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBCwOfQuadBC0
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.QuadBC2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
theorem UpperTheory.Gal.SV.quad_base_change_w_of_printed_results (_P : _root_.UpperTheory.V.Af.Hypotheses') : UpperTheory.V.Br.QuadBCw := by
  intro F E _ _ _ _ _ _ _ h2 a ha2 _ π hr
  obtain rfl := ha2.out
  exact (UpperTheory.ConvolutionTheory.R2.quadBC2 F E h2 π hr).imp_right fun ⟨P, hP⟩ => ⟨P, UpperTheory.V.Br.IsBCw.of_isBC hP⟩
end
