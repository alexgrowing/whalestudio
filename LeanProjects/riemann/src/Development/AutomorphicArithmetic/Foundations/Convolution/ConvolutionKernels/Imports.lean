import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalAdEq
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistExAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdBasic
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.K

theorem UpperTheory.ConvolutionTheory.K.g0 :
    G0 := by
  refine ⟨fun F E _ _ _ _ _ _ σ _ n _ μ _ => ?_, fun F _ _ n μ _ g => ?_⟩
  · obtain ⟨θ, h⟩ := galTwistEx E n μ σ.toRingEquiv
    exact ⟨θ, fun g => by rw [galAdEq]; exact h g⟩
  · rw [galAdEq]
    ext i j : 2
    exact ((adBasic F).2.1 _).symm
