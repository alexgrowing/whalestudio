import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreLift
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDesc
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftStep
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftAll
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.DescStep
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStrong
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Cbcc

theorem UpperTheory.ConvolutionTheory.T.cbcc_of_core (hC : UpperTheory.ConvolutionTheory.CI) (hG : UpperTheory.ConvolutionTheory.GM.GM) : UpperTheory.V.Z.Bc.CBCc :=
  have a := liftStep (coreLift hC hG)
  have b := liftAll a
  have c := descStep (coreDesc hC hG) b
  cbcc places a b c (splitStrong c)
