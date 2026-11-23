import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.atInj :
    UpperTheory.ConvolutionTheory.Dp.AtInj := by
  intro E _ _ _ n μ _ V V' hV hV' S hS t h h'
  obtain ⟨π, hπ, -⟩ := exCusp E n μ V hV
  obtain ⟨π', hπ', -⟩ := exCusp E n μ V' hV'
  have e : π = π' := by
    refine GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC E n π π' ?_)
    filter_upwards [hS.compl_mem_cofinite] with w hw
    obtain ⟨B, hB, h1⟩ := (sSatIff E n μ π V hπ w _).1 (h w hw)
    obtain ⟨B', hB', h2⟩ := (sSatIff E n μ π' V' hπ' w _).1 (h' w hw)
    have : B' = B := Multiset.map_injective (fun a b e => Units.ext e) (hB'.symm.trans hB)
    subst this
    exact ⟨B', h1, h2⟩
  subst e
  rw [((exSummand E n μ π V).1 hπ).2, ((exSummand E n μ π V').1 hπ').2]
