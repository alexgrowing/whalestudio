import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PMultC
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.isoEq :
    UpperTheory.ConvolutionTheory.Dp.IsoEq := by
  intro E _ _ _ n π π'
  constructor
  · intro h
    exact GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.cuspMultOneGL E n π π' ((Cm.mk_eq_mk_iff π π').2 ((Cm.iso_iff π π').1 h)))
  · rintro rfl
    exact (Cm.iso_iff π π).2 ((Cm.mk_eq_mk_iff π π).1 rfl)
