import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldMapSurjectiveOfMonoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkRetractionOfSmallLiftingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfLocalRetractionsModMaximalIdealPowStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open IsLocalRing

namespace GlobalTheory.ArtinOpen

theorem stalk_hom_ext_of_mono {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X) (R : CommRingCat.{0})
    [IsLocalRing R] (g₁ g₂ : X.presheaf.stalk x ⟶ R) [IsLocalHom g₁.hom] [IsLocalHom g₂.hom]
    (h : f.stalkMap x ≫ g₁ = f.stalkMap x ≫ g₂) : g₁ = g₂ := by
  have e : Spec.map g₁ ≫ X.fromSpecStalk x = Spec.map g₂ ≫ X.fromSpecStalk x := by
    rw [← cancel_mono f, Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, h]
  have e2 := (SpecToEquivOfLocalRing X R).symm.injective (a₁ := ⟨x, g₁, inferInstance⟩)
    (a₂ := ⟨x, g₂, inferInstance⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]; exact e)
  obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simpa using e3

theorem isOpenImmersion_of_lift : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [Mono f], (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → IsOpenImmersion f := by
  intro X Y f _ _ _ hlift
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Flat f := by
    refine (Flat.iff_flat_stalkMap f).2 fun x => ?_
    have hres := GlobalTheory.T.residueFieldMap_surjective_of_mono' f x
    refine GlobalTheory.T.flat_of_local_retractions_mod_maximalIdeal_pow (f.stalkMap x).hom (fun n => GlobalTheory.T.exists_stalk_retraction_of_small_lifting f hlift x hres n) ?_
    intro n g₁ g₂ h₁ h₂ h
    have := stalk_hom_ext_of_mono f x
      (CommRingCat.of (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ (n + 1)))
      (CommRingCat.ofHom g₁) (CommRingCat.ofHom g₂) (by ext a; exact congr($h a))
    exact congrArg CommRingCat.Hom.hom this
  exact IsOpenImmersion.of_flat_of_mono f

end GlobalTheory.ArtinOpen
