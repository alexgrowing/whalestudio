import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmoothOfIsDedekindDomain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsProperCurveThroughPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonzeroLocusSecPw
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.CurveThrough

theorem smooth_of_dedekind_charts (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0})
    (f : C ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (h : ∀ U : C.Opens, IsAffineOpen U → Nonempty U → IsDedekindDomain Γ(C, U)) :
    Smooth f := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Smooth)
    (fun U : {U : C.affineOpens // Nonempty U.1} => U.1) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, ⟨⟨x, hx⟩⟩⟩, hx⟩
  · rintro ⟨⟨U, hU⟩, hne⟩
    haveI := h U hU hne
    have hft : (f.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨⊤, isAffineOpen_top _⟩
        ⟨U, hU⟩ le_top
    let e := Scheme.ΓSpecIso (CommRingCat.of k)
    let φ : k →+* Γ(C, U) := (e.inv ≫ f.appLE ⊤ U le_top).hom
    have hφ : φ.FiniteType :=
      (RingHom.finiteType_respectsIso.cancel_left_isIso e.inv (f.appLE ⊤ U le_top)).2 hft
    have hs : φ.Smooth := by
      letI := φ.toAlgebra
      haveI : Algebra.FiniteType k Γ(C, U) := hφ
      exact GlobalTheory.DedekindSmooth.smooth_of_isDedekindDomain k Γ(C, U)
    exact (RingHom.Smooth.propertyIsLocal.respectsIso.cancel_left_isIso e.inv (f.appLE ⊤ U le_top)).1 hs

end GlobalTheory.CurveThrough
