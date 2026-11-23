import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalEquiv
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TwOpEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.PresOfOrder
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdHeight
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.CommProj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.galTwistEx :
    GalTwistEx := by
  intro K _ _ n μ _ σ
  obtain ⟨e, he, he', hg, m, hm, hit⟩ := galEquiv K n σ
  have hp := presOfOrder μ e m hm hit
  have hp' : MeasurePreserving e.symm μ μ := hp.symm e.toHomeomorph.toMeasurableEquiv
  have hg' : ∀ g, e.symm g ∈ Gam K n ↔ g ∈ Gam K n := fun g => by rw [← hg, e.apply_symm_apply]
  obtain ⟨U, hU, hU'⟩ := twOpEx K n μ e hg hp
  refine ⟨⟨e, hg, hp, ⟨1, 1, fun g => ?_⟩, U, hU, ?_⟩, he⟩
  · rw [he, adHeight]; simp
  · exact commProj (cuspidalL2 μ) U (fun v hv => galCusp K n μ σ.symm e.symm he' hg' hp' v _ hv (hU v))
      (fun v hv => galCusp K n μ σ e he hg hp v _ hv (hU' v))
