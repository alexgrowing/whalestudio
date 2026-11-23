import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem exists_grpObj_isAbelianScheme_of_isPullback_spMap : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  intro R _ A _ g hA hg R' _ σ X' s' φ h
  have hsm : SmoothOfRelativeDimension g s' := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg
  let B := (Over.pullback (spMap σ)).obj A
  letI : GrpObj B := Functor.grpObjObj
  let e : B ≅ Over.mk s' := Over.isoMk h.isoPullback.symm (by simp [B])
  letI : GrpObj (Over.mk s') := GrpObj.ofIso e
  refine ⟨this, ?_, hsm⟩
  have hc := hA.comm
  have hcB : IsCommMonObj B := Functor.isCommMonObj_obj
  exact {
    comm := by
      constructor
      show (β_ _ _).hom ≫ ((e.inv ⊗ₘ e.inv) ≫ μ[B] ≫ e.hom) = (e.inv ⊗ₘ e.inv) ≫ μ[B] ≫ e.hom
      rw [← Category.assoc, ← BraidedCategory.braiding_naturality, Category.assoc,
        ← Category.assoc (β_ B B).hom, IsCommMonObj.mul_comm]
    smooth := MorphismProperty.of_isPullback (P := @Smooth) h hA.smooth
    proper := MorphismProperty.of_isPullback (P := @IsProper) h hA.proper
    geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hA.geomConnected }

end GlobalTheory
