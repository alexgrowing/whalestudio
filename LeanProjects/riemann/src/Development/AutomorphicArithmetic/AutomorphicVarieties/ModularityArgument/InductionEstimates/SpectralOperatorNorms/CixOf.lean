import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Ci
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FinsumSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.KillEx2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.OneSideX
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FamEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ExistsPositivePeriodLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PairFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ImportsAlt

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.Ci UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial in

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.cix_of (hK : KernX) (hT : ForAllC fun _ _ _ μ _ _ _ _ _ _ _ _ A A' => TruncCpt μ A A') : CIx :=
  cixOf Dp.parEx (trExp expForm) (evVal evEx Dp.parEx) valBc killEx2 kfBc truncSpec sepPoly
    (oneSide K.kern2 C.polyBdAll C.smoothDecay C.decayTraceClass C.cuspTrBand Dp.multiplicity_one_cuspidal_spectrum_normOneGL evEx) (oneSideX hK evEx) evEx kill
    killExempt (famEx hT unitB pairFacts UpperTheory.V.Z.IntegralApplyAeEq.main)
