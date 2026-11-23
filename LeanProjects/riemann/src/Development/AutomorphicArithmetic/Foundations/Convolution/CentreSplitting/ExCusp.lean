import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.exCusp :
    UpperTheory.ConvolutionTheory.Dp.ExCusp := by
  intro E _ _ _ n μ _ V hV
  obtain ⟨hs, hne, hirr, -⟩ := formsIrr E n μ V hV
  refine ⟨Cm.ofIrr _ hs (hs.isIrreducible_iff.2 ⟨hne, hirr⟩), ⟨hV, Cm.carrier_ofIrr _ _ _⟩, fun π h => ?_⟩
  refine GlobalTheory.CuspRep.CuspSub.ext ?_
  rw [← Cm.map_carrier π, h.carrier_eq]
  rfl
