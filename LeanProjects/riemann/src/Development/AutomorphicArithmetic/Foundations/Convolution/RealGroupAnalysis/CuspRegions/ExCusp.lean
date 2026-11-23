import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.CuspRegions.CarrierEq

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dr.exCusp :
    UpperTheory.ConvolutionTheory.Dr.ExCusp := by
  intro E _ _ _ n μ _ V hV
  obtain ⟨hs, hne, hirr, -⟩ := formsIrr E n μ V hV
  refine ⟨Fb.ofIrr _ hs (hs.isIrreducible_iff.2 ⟨hne, hirr⟩), ⟨hV, Fb.carrier_ofIrr _ _ _⟩, fun π h => ?_⟩
  refine TR.CuspSub.ext ?_
  rw [← Fb.map_carrier π, h.carrier_eq]
  rfl
