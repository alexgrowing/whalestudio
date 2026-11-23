import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush

theorem exists_functionField_map_of_genericPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K)
      (ζ : Sp K ⟶ W.Z), ζ (IsLocalRing.closedPoint K) = genericPoint W.Z → ζ ≫ W.p₁ = spMap ψ₁ ≫ (ratOf Y).pt →
        ζ ≫ W.p₂ = spMap ψ₂ ≫ (ratOf Y).pt → ∃ j : W.Z.functionField →+* K, j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  intro F _ Y W K _ ψ₁ ψ₂ ζ h h₁ h₂
  have hs : ζ (IsLocalRing.closedPoint K) ⤳ genericPoint W.Z := h ▸ specializes_rfl
  let j : W.Z.functionField →+* K :=
    (W.Z.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := .of K) ζ).hom
  have e : spMap j ≫ W.Z.fromSpecStalk (genericPoint W.Z) = ζ := by
    change Spec.map (CommRingCat.ofHom j) ≫ W.Z.fromSpecStalk (genericPoint W.Z) = ζ
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo ζ
  have key : ∀ (p : W.Z ⟶ Y.X) [IsDominant p] (ψ : Y.Fn →+* K), ζ ≫ p = spMap ψ ≫ (ratOf Y).pt →
      j.comp (functionFieldMap p) = ψ := by
    intro p _ ψ hp
    have e2 : spMap (j.comp (functionFieldMap p)) ≫ Y.X.fromSpecStalk (genericPoint Y.X) =
        spMap ψ ≫ Y.X.fromSpecStalk (genericPoint Y.X) := by
      change Spec.map (CommRingCat.ofHom (j.comp (functionFieldMap p))) ≫ genericFieldPoint Y.X = _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, specMap_functionFieldMap,
        ← Category.assoc]
      change (spMap j ≫ W.Z.fromSpecStalk (genericPoint W.Z)) ≫ p = _
      rw [e, hp]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp e2))
  exact ⟨j, key W.p₁ ψ₁ h₁, key W.p₂ ψ₂ h₂⟩

end GlobalTheory.FlagPush
