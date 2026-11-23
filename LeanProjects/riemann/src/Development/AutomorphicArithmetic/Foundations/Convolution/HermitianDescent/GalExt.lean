import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

theorem UpperTheory.ConvolutionTheory.D.galExt :
    UpperTheory.ConvolutionTheory.D.GalExt := by
  intro F E k _ _ _ _ _ σ q h
  exact (UpperTheory.ConvolutionTheory.D.galBase F E k σ q h).2.2.2
