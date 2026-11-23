import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Matched
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem germ_appLE_eq_gm_val {Y X : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (O : Y.Opens) (hle : O ≤ f ⁻¹ᵁ U)
    (y : Y) (hy : y ∈ O) (a : Γ(X, U)ˣ) :
    (Y.presheaf.germ O y hy).hom ((f.appLE U O hle).hom a.val) = (gm f y U a).val := by
  rw [gm_val f y U (hle hy)]
  exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hle) y hy _

theorem exists_unit_of_glues : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (V : X.Opens) (a : Γ(X', p ⁻¹ᵁ V)ˣ) (b : Γ(Z, i ⁻¹ᵁ V)ˣ), (∀ z : Z', p (i' z) ∈ V → gm i' z (p ⁻¹ᵁ V) a = gm p' z (i ⁻¹ᵁ V) b) → ∃ u : Γ(X, V)ˣ, (∀ x' : X', p x' ∈ V → gm p x' V u = gm (𝟙 X') x' (p ⁻¹ᵁ V) a) ∧ (∀ z : Z, i z ∈ V → gm i z V u = gm (𝟙 Z) z (i ⁻¹ᵁ V) b) := by
  intro X X' Z Z' p i i' p' _ hG V a b hab
  have key : ∀ (a : Γ(X', p ⁻¹ᵁ V)ˣ) (b : Γ(Z, i ⁻¹ᵁ V)ˣ),
      (∀ z : Z', p (i' z) ∈ V → gm i' z (p ⁻¹ᵁ V) a = gm p' z (i ⁻¹ᵁ V) b) →
      ∃! s : Γ(X, V), (p.app V).hom s = a.val ∧ (i.app V).hom s = b.val := by
    intro a b hab
    apply hG V
    apply TopCat.Presheaf.section_ext Z'.sheaf
    intro z hz
    exact (germ_appLE_eq_gm_val i' _ _ inf_le_left z hz a).trans
      ((congrArg Units.val (hab z hz.1)).trans (germ_appLE_eq_gm_val p' _ _ inf_le_right z hz b).symm)
  obtain ⟨s, ⟨hs₁, hs₂⟩, -⟩ := key a b hab
  obtain ⟨t, ⟨ht₁, ht₂⟩, -⟩ := key a⁻¹ b⁻¹ (fun z hz => by rw [map_inv, map_inv, hab z hz])
  have h₁ := key 1 1 (fun z _ => by rw [map_one, map_one])
  have e : s * t = 1 := by
    apply h₁.unique
    · constructor
      · rw [map_mul, hs₁, ht₁, Units.mul_inv, Units.val_one]
      · rw [map_mul, hs₂, ht₂, Units.mul_inv, Units.val_one]
    · constructor
      · rw [map_one, Units.val_one]
      · rw [map_one, Units.val_one]
  refine ⟨⟨s, t, e, (mul_comm _ _).trans e⟩, fun x hx => ?_, fun x hx => ?_⟩
  · apply Units.ext
    rw [gm_val p x V hx, gm_val (𝟙 X') x (p ⁻¹ᵁ V) hx]
    exact congrArg (X'.presheaf.germ (p ⁻¹ᵁ V) x hx).hom hs₁
  · apply Units.ext
    rw [gm_val i x V hx, gm_val (𝟙 Z) x (i ⁻¹ᵁ V) hx]
    exact congrArg (Z.presheaf.germ (i ⁻¹ᵁ V) x hx).hom hs₂

end GlobalTheory.PinchLift
