import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsTw
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ConjCarries
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.GalCentral
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceC

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.conjIff :
    UpperTheory.ConvolutionTheory.Dp.ConjIff := by
  intro E _ _ _ n μ _ θ σ s hs he π V hV
  constructor
  · intro h
    obtain ⟨P', hsp, hiso⟩ := h s hs
    cases P' with
    | cx π' =>
      have e : π' = π := (UpperTheory.ConvolutionTheory.Dp.isoEq E n π' π).1 hiso
      subst e
      have h1 := (UpperTheory.ConvolutionTheory.Dp.conjCarries E n μ θ σ s hs he π' π' V hsp).1 hV
      exact ((UpperTheory.ConvolutionTheory.Dp.exSummand E n μ π' _).1 h1).2.trans ((UpperTheory.ConvolutionTheory.Dp.exSummand E n μ π' _).1 hV).2.symm
    | re π' => exact hiso.elim
  · intro h s' hs'
    obtain rfl : s' = s := (UpperTheory.ConvolutionTheory.Dp.galCentral E n σ s hs).1 s' hs'
    obtain ⟨π', hsp⟩ := UpperTheory.CBC.SConjSpaceC_holds E σ s' hs n π
    have h1 : Carries μ π' V :=
      (UpperTheory.ConvolutionTheory.Dp.conjCarries E n μ θ σ s' hs he π π' V hsp).2 (by rw [h]; exact hV)
    have e : π' = π := (UpperTheory.ConvolutionTheory.Dp.exCusp E n μ V hV.summand).unique h1 hV
    exact ⟨.cx π', hsp, (UpperTheory.ConvolutionTheory.Dp.isoEq E n π' π).2 e⟩
