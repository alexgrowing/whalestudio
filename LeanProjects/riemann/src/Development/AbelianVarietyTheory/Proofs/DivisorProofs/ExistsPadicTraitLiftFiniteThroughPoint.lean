import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_lift_finite_through_point : ∀ (X Z : Scheme.{0}) (f : X ⟶ Z), IsFinite f → ∀ (p : ℕ) [Fact p.Prime] (Y : Sp (OO p) ⟶ Z) (w : X), f w = (gPt p ≫ Y) (IsLocalRing.closedPoint (PadicAlgCl p)) → ∃ y : Sp (OO p) ⟶ X, y ≫ f = Y ∧ (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) = w := by
  intro X Z f hf p _ Y w hw

  set x : Sp (PadicAlgCl p) ⟶ Z := gPt p ≫ Y with hxdef
  obtain ⟨⟨z, φ⟩, hzφ⟩ := (Scheme.SpecToEquivOfField (PadicAlgCl p) Z).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hzφ
  have hz : f w = z := by
    rw [hw, ← hzφ]
    exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply z _)
  subst hz
  have hfin := GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite f w
  letI := (f.residueFieldMap w).hom.toAlgebra
  letI := φ.hom.toAlgebra
  haveI : Module.Finite (Z.residueField (f w)) (X.residueField w) := hfin
  haveI : Algebra.IsAlgebraic (Z.residueField (f w)) (X.residueField w) := inferInstance
  let ψ : X.residueField w →ₐ[Z.residueField (f w)] PadicAlgCl p := IsAlgClosed.lift
  set y0 : Sp (PadicAlgCl p) ⟶ X := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField w with hy0
  have hy0f : y0 ≫ f = gPt p ≫ Y := by
    rw [← hxdef, ← hzφ, hy0, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact ψ.commutes a
  have hy0w : y0 (IsLocalRing.closedPoint (PadicAlgCl p)) = w :=
    (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply w _)

  haveI : IsProper f := inferInstance
  have hE : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f).1
  obtain ⟨⟨l, hl1, hl2⟩⟩ := (hE { R := OO p, K := PadicAlgCl p, i₁ := y0, i₂ := Y, commSq := ⟨hy0f⟩ }).exists_lift
  refine ⟨l, hl2, ?_⟩
  have : gPt p ≫ l = y0 := hl1
  rw [this, hy0w]

end GlobalTheory.UPoinc
