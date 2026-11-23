import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.KillEx
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.killEx2 :
    KillEx2 := by
  intro F E _ _ _ _ _ _ _ n SE SF hS B B' _ _ b b' hb hb' L t hc h h'
  exact UpperTheory.ConvolutionTheory.Ci.killEx_listed UpperTheory.ConvolutionTheory.Dp.parEx F E n SE SF hS B B' b b' hb hb' L t hc h h'
