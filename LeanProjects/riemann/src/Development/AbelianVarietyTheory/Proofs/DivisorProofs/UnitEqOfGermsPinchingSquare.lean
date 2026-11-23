import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchLift

theorem unit_eq_of_germs_glues : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (V : X.Opens) (u v : Γ(X, V)ˣ), (∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) → (∀ z : Z, i z ∈ V → gm i z V u = gm i z V v) → u = v := by
  intro X X' Z Z' p i i' p' hc hG V u v hp hi
  have ep : (p.app V).hom u.val = (p.app V).hom v.val := by
    apply TopCat.Presheaf.section_ext X'.sheaf (p ⁻¹ᵁ V)
    intro x hx
    have h := congrArg Units.val (hp x hx)
    rwa [gm_val _ x V hx, gm_val _ x V hx] at h
  have ei : (i.app V).hom u.val = (i.app V).hom v.val := by
    apply TopCat.Presheaf.section_ext Z.sheaf (i ⁻¹ᵁ V)
    intro z hz
    have h := congrArg Units.val (hi z hz)
    rwa [gm_val _ z V hz, gm_val _ z V hz] at h
  have key : ∀ (f g : Z' ⟶ X) (_ : f = g) (O : Z'.Opens) (e : O ≤ f ⁻¹ᵁ V) (e' : O ≤ g ⁻¹ᵁ V),
      f.appLE V O e = g.appLE V O e' := by
    intro f g hfg O e e'; subst hfg; rfl
  have hag : (i'.appLE (p ⁻¹ᵁ V) (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left).hom ((p.app V).hom u.val) =
      (p'.appLE (i ⁻¹ᵁ V) (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_right).hom ((i.app V).hom u.val) := by
    have e1 := Scheme.Hom.comp_appLE i' p V (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left
    have e2 := Scheme.Hom.comp_appLE p' i V (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_right
    have e3 := key _ _ hc (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left inf_le_right
    rw [e1, e2] at e3
    have := congrArg (fun f => f.hom u.val) e3
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  exact Units.ext ((hG V _ _ hag).unique ⟨rfl, rfl⟩ ⟨ep.symm, ei.symm⟩)

end GlobalTheory.PinchLift
