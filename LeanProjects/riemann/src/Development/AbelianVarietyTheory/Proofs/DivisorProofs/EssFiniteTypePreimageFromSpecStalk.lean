import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegResidueFieldOfIsOpenImmersion
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothStalk

theorem essFiniteType_preimage_fromSpecStalk (F : Type) [CommRing F] (X : Scheme.{0})
    (g : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType g] (z : X) :
    (Spec.preimage (X.fromSpecStalk z ≫ g)).hom.EssFiniteType := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ g)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have he : Spec.preimage (X.fromSpecStalk z ≫ g) = φ ≫ X.presheaf.germ U z hx := by
    rw [← Spec.map_inj, Spec.map_preimage, Spec.map_comp, hφ, ← hU.fromSpecStalk_eq_fromSpecStalk hx,
      IsAffineOpen.fromSpecStalk, Category.assoc]
  rw [he, CommRingCat.hom_comp]
  refine RingHom.EssFiniteType.comp hft.essFiniteType ?_
  let _ := X.presheaf.algebra_section_stalk ⟨z, hx⟩
  have := hU.isLocalization_stalk ⟨z, hx⟩
  exact Algebra.EssFiniteType.of_isLocalization (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hx⟩).asIdeal.primeCompl

theorem stalk_regular_essFiniteType_dim : ∀ (F : Type) [Field F] (Cs : Scheme.{0}) (g : Cs ⟶ Sp F) (n : ℕ), SmoothOfRelativeDimension n g → ∀ z : Cs, IsRegularLocalRing (Cs.presheaf.stalk z) ∧ ∃ b : F →+* Cs.presheaf.stalk z, Cs.fromSpecStalk z ≫ g = spMap b ∧ b.EssFiniteType ∧ (letI := ((residue (Cs.presheaf.stalk z)).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim (Cs.presheaf.stalk z) = a ∧ Algebra.trdeg F (ResidueField (Cs.presheaf.stalk z)) = t ∧ a + t = n) := by
  intro F _ Cs g n hsm z
  haveI := hsm
  haveI : Smooth g := SmoothOfRelativeDimension.smooth n g
  haveI : IsRegularRing (CommRingCat.of F) := inferInstanceAs (IsRegularRing F)
  have hreg : ∀ x : Cs, IsRegularLocalRing (Cs.presheaf.stalk x) := fun x =>
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth g x
  refine ⟨hreg z, (Spec.preimage (Cs.fromSpecStalk z ≫ g)).hom, ?_, essFiniteType_preimage_fromSpecStalk F Cs g z, ?_⟩
  · exact (Spec.map_preimage _).symm
  · have h := GlobalTheory.StalkDim.stalk_dim_add_trdeg F g (𝟙 Cs) n (by simp) (by simpa using hsm)
      (fun x => haveI := hreg x; ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing) z
    have he : Spec.preimage (Cs.fromSpecResidueField z ≫ g) =
        Spec.preimage (Cs.fromSpecStalk z ≫ g) ≫ Cs.residue z := by
      rw [← Spec.map_inj, Spec.map_preimage, Spec.map_comp, Spec.map_preimage, Scheme.fromSpecResidueField,
        Category.assoc]
    rw [he] at h
    exact h

end GlobalTheory.SmoothStalk
