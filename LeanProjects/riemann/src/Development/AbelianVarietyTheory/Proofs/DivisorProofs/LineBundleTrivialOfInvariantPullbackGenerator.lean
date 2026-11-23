import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentitySnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.DescGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFlat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

section Descent

variable {X Y : Scheme.{0}}

lemma appLE_eq_of_eq_hom {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

lemma opens_toTop_bijective (U : X.Opens) : Function.Bijective (U.ι.appLE U ⊤ U.ι_preimage_self.ge) := by
  have e : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]; rfl
  rw [e]
  exact ConcreteCategory.bijective_of_isIso U.topIso.inv

example (p : X ⟶ Y) [Flat p] [Surjective p] [IsAffineHom p] (V : Y.Opens) :
    Flat (p ∣_ V) ∧ Surjective (p ∣_ V) ∧ IsAffineHom (p ∣_ V) :=
  ⟨inferInstance, IsZariskiLocalAtTarget.restrict ‹_› V, by first | exact HasAffineProperty.restrict ‹_› V | exact IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) ‹_› V | exact (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (isPullback_morphismRestrict p V).flip ‹_›) | exact (inferInstance : IsAffineHom (p.resLE V (p ⁻¹ᵁ V) le_rfl))⟩

lemma restrict_appTop_toTop (p : X ⟶ Y) (V : Y.Opens) (a : Γ(Y, V)) :
    (p ∣_ V).appTop (V.ι.appLE V ⊤ V.ι_preimage_self.ge a) =
      (p ⁻¹ᵁ V).ι.appLE (p ⁻¹ᵁ V) ⊤ (p ⁻¹ᵁ V).ι_preimage_self.ge (p.app V a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg _ (appLE_eq_of_eq_hom (morphismRestrict_ι p V) _ _ _)

lemma restrict_props (p : X ⟶ Y) [Flat p] [Surjective p] [IsAffineHom p] (V : Y.Opens) :
    Flat (p ∣_ V) ∧ Surjective (p ∣_ V) ∧ IsAffineHom (p ∣_ V) :=
  ⟨inferInstance, IsZariskiLocalAtTarget.restrict ‹_› V, by first | exact HasAffineProperty.restrict ‹_› V | exact IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) ‹_› V | exact (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (isPullback_morphismRestrict p V).flip ‹_›) | exact (inferInstance : IsAffineHom (p.resLE V (p ⁻¹ᵁ V) le_rfl))⟩

lemma appTop_toTop (V : X.Opens) {Z : Scheme.{0}} (y : Z ⟶ V.toScheme) (s : Γ(X, V)) :
    y.appTop (V.ι.appLE V ⊤ V.ι_preimage_self.ge s) =
      (y ≫ V.ι).appLE V ⊤ (fun z _ => (y z).2) s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]
  rfl

theorem exists_app_eq_of_invariant (p : X ⟶ Y) [Flat p] [Surjective p] [IsAffineHom p] (V : Y.Opens)
    (s : Γ(X, p ⁻¹ᵁ V))
    (hs : ∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ X), y₁ ≫ p = y₂ ≫ p → ∀ (h₁ : ⊤ ≤ y₁ ⁻¹ᵁ (p ⁻¹ᵁ V))
      (h₂ : ⊤ ≤ y₂ ⁻¹ᵁ (p ⁻¹ᵁ V)), y₁.appLE _ ⊤ h₁ s = y₂.appLE _ ⊤ h₂ s) :
    ∃ a : Γ(Y, V), p.app V a = s := by
  obtain ⟨h1, h2, h3⟩ := restrict_props p V
  obtain ⟨v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.descend_gen (p ∣_ V)
    ((p ⁻¹ᵁ V).ι.appLE (p ⁻¹ᵁ V) ⊤ (p ⁻¹ᵁ V).ι_preimage_self.ge s) (fun y₁ y₂ h => by
      rw [appTop_toTop, appTop_toTop]
      refine hs _ _ _ ?_ _ _
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, h, Category.assoc])
  obtain ⟨a, rfl⟩ := (opens_toTop_bijective V).2 v
  refine ⟨a, (opens_toTop_bijective (p ⁻¹ᵁ V)).1 ?_⟩
  rw [← restrict_appTop_toTop]
  exact hv

lemma app_map_homOfLE (p : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    p.app V (Y.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (fun _ hx => h hx : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U)).op (p.app U a) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

end Descent

open ReciprocityTheory.ChartRestriction.G.DVR.TG in

theorem triv_of_isPullGen_of_invariant : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y), Flat p → Surjective p → IsAffineHom p → ∀ (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → (∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ X), y₁ ≫ p = y₂ ≫ p → ∀ (k : M.ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)), res h₁ (pullU y₁ _ (e k)) = res h₂ (pullU y₂ _ (e k))) → Triv M := by
  intro X Y p _ _ _ M e he hinv
  have hval : ∀ (k : M.ι) (u : Γ(X, p ⁻¹ᵁ M.U k)ˣ), (u = e k ∨ u = (e k)⁻¹) →
      ∃ a : Γ(Y, M.U k), p.app _ a = u := by
    intro k u hu
    refine exists_app_eq_of_invariant p (M.U k) u ?_
    intro Z y₁ y₂ hy h₁ h₂
    have H := hinv Z y₁ y₂ hy k ⊤ h₁ h₂
    rcases hu with rfl | rfl
    · exact congrArg Units.val H
    · have H' := congrArg (fun x => x⁻¹) H
      simp only [← map_inv] at H'
      exact congrArg Units.val H'
  choose f hf using fun k => hval k (e k) (Or.inl rfl)
  choose f' hf' using fun k => hval k (e k)⁻¹ (Or.inr rfl)
  have inj := fun V => app_injective_of_flat_surj p V
  have hmul : ∀ k, f k * f' k = 1 := fun k =>
    inj _ (by rw [map_mul, map_one, hf, hf', Units.mul_inv])
  let fu : ∀ k, Γ(Y, M.U k)ˣ := fun k => ⟨f k, f' k, hmul k, by rw [mul_comm]; exact hmul k⟩
  refine ⟨⟨fu⟩, fun i j => Units.ext (inj _ ?_)⟩
  have H := congrArg Units.val
    (he i j (p ⁻¹ᵁ (M.U i ⊓ M.U j)) (fun _ hx => hx.1) (fun _ hx => hx.2) le_rfl)
  have eX : ∀ {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ),
      ((res h a : Γ(X, V)ˣ) : Γ(X, V)) = X.presheaf.map (homOfLE h).op a := fun _ _ => rfl
  have eY : ∀ {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)ˣ),
      ((res h a : Γ(Y, V)ˣ) : Γ(Y, V)) = Y.presheaf.map (homOfLE h).op a := fun _ _ => rfl
  have eP : ((pullU p (M.U i ⊓ M.U j) (M.g i j) : Γ(X, p ⁻¹ᵁ (M.U i ⊓ M.U j))ˣ) : Γ(X, p ⁻¹ᵁ (M.U i ⊓ M.U j))) =
      p.app _ (M.g i j) := rfl
  have eid : X.presheaf.map (homOfLE (le_rfl : p ⁻¹ᵁ (M.U i ⊓ M.U j) ≤ p ⁻¹ᵁ (M.U i ⊓ M.U j))).op =
      𝟙 _ := by
    rw [show homOfLE (le_rfl : p ⁻¹ᵁ (M.U i ⊓ M.U j) ≤ _) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  simp only [Units.val_mul, eX, eP] at H
  rw [eid, CommRingCat.id_apply] at H
  simp only [Units.val_mul, map_mul, eY, app_map_homOfLE]
  show X.presheaf.map _ (p.app _ (f i)) = _ * X.presheaf.map _ (p.app _ (f j))
  rw [hf, hf]
  exact H

end GlobalTheory.CharKer
