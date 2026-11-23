import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.Blowup

theorem comap_ι_support_compl_eq_top {X : Scheme.{u}} (Z : X.IdealSheafData) :
    Z.comap (Scheme.Opens.ι Z.support.compl) = ⊤ := by
  refine comap_eq_top_of_notMem_support _ Z fun x => ?_
  show x.1 ∉ Z.support
  exact x.2

theorem blowupIsIsoOffCenter : BlowupIsIsoOffCenter.{u} := by
  intro X X' π Z h
  have h1 := h.restrict Z.support.compl
  rw [comap_ι_support_compl_eq_top Z] at h1
  exact h1.isIso_of_top

end FunctorialResolution.Blowup
