import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.NotConjIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.IndNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.CoreInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.Cix
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CbccOfCore
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Ci
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.GmOfBcfl

open UpperTheory.ConvolutionTheory UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indCs_of_gm (hG : GM.GM) : IndCs :=
  indCs (indNorm (coreInd cix hG (T.liftAll (T.liftStep (T.coreLift ci hG)))))

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indCs_of_bcfl (h : PositivityTheory.Rg.Tf.Loc.BCFLUnit) : IndCs :=
  indCs_of_gm (GM.gm_of_bcfl h)
