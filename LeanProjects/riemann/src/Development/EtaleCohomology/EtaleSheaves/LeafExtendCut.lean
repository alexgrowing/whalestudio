import Development.EtaleCohomology.EtaleSheaves.LeafCurveVCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafExtendCut

def LeafStalkValuation : Prop := ∀ (Ω : Type) [Field Ω] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp Ω) (x y : C)
  (hx : IsGenericPoint x (⊤ : Set C)), IsCurve c → y ≠ x →
    ValuationRing (C.presheaf.stalk y) ∧
      (letI := (C.presheaf.stalkSpecializes (hx.specializes (Set.mem_univ y))).hom.toAlgebra
       IsFractionRing (C.presheaf.stalk y) (C.presheaf.stalk x))

def LeafLocalExtend : Prop := ∀ {C X S : Scheme.{0}} [IsIntegral C] (sC : C ⟶ S) (p : X ⟶ S) [IsProper p] (x y : C),
  IsGenericPoint x (⊤ : Set C) → ∀ (h : x ⤳ y), ValuationRing (C.presheaf.stalk y) →
    (letI := (C.presheaf.stalkSpecializes h).hom.toAlgebra
     IsFractionRing (C.presheaf.stalk y) (C.presheaf.stalk x)) →
    ∀ ψ : Spec (C.presheaf.stalk x) ⟶ X, ψ ≫ p = C.fromSpecStalk x ≫ sC →
      ∃ (U : C.Opens) (_ : y ∈ U) (hxU : x ∈ U) (f : U.toScheme ⟶ X),
        U.fromSpecStalkOfMem x hxU ≫ f = ψ ∧ f ≫ p = U.ι ≫ sC

def LeafGlueExtend : Prop := ∀ {C X S : Scheme.{0}} [IsIntegral C] (sC : C ⟶ S) (p : X ⟶ S) [IsSeparated p] (x : C),
  IsGenericPoint x (⊤ : Set C) → ∀ ψ : Spec (C.presheaf.stalk x) ⟶ X,
    (∀ y : C, ∃ (U : C.Opens) (_ : y ∈ U) (hxU : x ∈ U) (f : U.toScheme ⟶ X),
        U.fromSpecStalkOfMem x hxU ≫ f = ψ ∧ f ≫ p = U.ι ≫ sC) →
      ∃ e : C ⟶ X, C.fromSpecStalk x ≫ e = ψ ∧ e ≫ p = sC

theorem goal_of (h1 : LeafStalkValuation) (h2 : LeafLocalExtend) (h3 : LeafGlueExtend) :
    LateralTheory.E.LeafCurveVCut.LeafExtend := by
  intro k Ω _ _ _ X C0 p _ c0 x hc hx ψ hψ
  have : IsIntegral C0 := hc.1
  refine h3 (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p x hx ψ ?_
  intro y
  by_cases hyx : y = x
  · subst hyx
    obtain ⟨U, hxU, f, hf1, hf2⟩ := spread_out_of_isGermInjective'
      (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p ψ hψ
    exact ⟨U, hxU, hxU, f, hf1.symm, hf2⟩
  · obtain ⟨hv, hfr⟩ := h1 Ω c0 x y hx hc hyx
    exact h2 (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p x y hx _ hv hfr ψ hψ

end LateralTheory.E.LeafExtendCut
