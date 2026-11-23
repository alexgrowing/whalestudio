import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential

namespace UpperTheory.Gal.FixZ

private def secEquiv {Y Y' : Scheme.{0}} {t : Y ⟶ Sp ℂ} {t' : Y' ⟶ Sp ℂ} (e : Y ≅ Y')
    (ht : e.hom ≫ t' = t) (V : Y'.Opens) : Sec t' V ≃ₐ[ℂ] Sec t (e.hom ⁻¹ᵁ V) :=
  AlgEquiv.ofBijective
    { appSec t' t e.hom V with
      commutes' := fun r => (semiHom_appSec ht V).map_algebraMap r }
    (ConcreteCategory.bijective_of_isIso (e.hom.app V))

private theorem eq_self_of_fix_D_of_linear_kaehler {A : Type} [CommRing A] [Algebra ℂ A] (g : Ω[A⁄ℂ] →ₗ[ℂ] Ω[A⁄ℂ])
    (hD : ∀ a, g (D ℂ A a) = D ℂ A a) (hs : ∀ (a : A) (ω : Ω[A⁄ℂ]), g (a • ω) = a • g ω)
    (ω : Ω[A⁄ℂ]) : g ω = ω := by
  have hω : ω ∈ Submodule.span A (Set.range (D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact hD a
  | zero => exact map_zero g
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [hs, hx]

private theorem exists_kaehler_map_D_of_algHom {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) :
    ∃ Ψ : Ω[A⁄ℂ] →ₗ[ℂ] Ω[B⁄ℂ], (∀ a, Ψ (D ℂ A a) = D ℂ B (f a)) ∧
      ∀ (a : A) (ω : Ω[A⁄ℂ]), Ψ (a • ω) = f a • Ψ ω := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : SMulCommClass ℂ A B := ⟨fun r a b => by
    change r • (f a * b) = f a * (r • b)
    rw [mul_smul_comm]⟩
  refine ⟨(KaehlerDifferential.map ℂ ℂ A B).restrictScalars ℂ, fun a => ?_, fun a ω => ?_⟩
  · exact KaehlerDifferential.map_D ℂ ℂ A B a
  · rw [LinearMap.restrictScalars_apply, LinearMap.map_smul, ← algebraMap_smul (A := B) a]
    rfl

private theorem exists_kaehler_equiv_D_of_algEquiv {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A ≃ₐ[ℂ] B) :
    ∃ Ψ : Ω[A⁄ℂ] ≃ₗ[ℂ] Ω[B⁄ℂ], (∀ a, Ψ (D ℂ A a) = D ℂ B (f a)) ∧
      ∀ (a : A) (ω : Ω[A⁄ℂ]), Ψ (a • ω) = f a • Ψ ω := by
  obtain ⟨Ψ, h1, h2⟩ := exists_kaehler_map_D_of_algHom (f : A →ₐ[ℂ] B)
  obtain ⟨Φ, g1, g2⟩ := exists_kaehler_map_D_of_algHom (f.symm : B →ₐ[ℂ] A)
  have l : ∀ ω, Φ (Ψ ω) = ω := eq_self_of_fix_D_of_linear_kaehler (Φ ∘ₗ Ψ)
    (fun a => by simp [h1, g1]) (fun a ω => by simp [h2, g2])
  have r : ∀ η, Ψ (Φ η) = η := eq_self_of_fix_D_of_linear_kaehler (Ψ ∘ₗ Φ)
    (fun a => by simp [h1, g1]) (fun a ω => by simp [h2, g2])
  exact ⟨LinearEquiv.ofLinear Ψ Φ (LinearMap.ext r) (LinearMap.ext l), h1, h2⟩

private theorem valR_comp_eq_valR_app {X W : Scheme} (x : Sp ℂ ⟶ X) (f : X ⟶ W) (V : W.Opens)
    (g : Γ(W, V)) :
    valR (x ≫ f) V g = valR x (f ⁻¹ᵁ V) (f.app V g) := by
  unfold valR
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ V)
  · have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ V := h
    rw [dif_pos h', dif_pos h]
    simp [Scheme.Hom.comp_appLE]
  · have h' : ¬ ⊤ ≤ (x ≫ f) ⁻¹ᵁ V := h
    rw [dif_neg h', dif_neg h]

private theorem preimage_le_preimage_preimage_of_comm_iso {Y Y' Z Z' : Scheme} (eY : Y ≅ Y') (eZ : Z ≅ Z') (c : Y ⟶ Z)
    (c' : Y' ⟶ Z') (hc : c ≫ eZ.hom = eY.hom ≫ c') (U' : Z'.Opens) (V' : Y'.Opens)
    (h : V' ≤ c' ⁻¹ᵁ U') : eY.hom ⁻¹ᵁ V' ≤ c ⁻¹ᵁ eZ.hom ⁻¹ᵁ U' := by
  rw [← Scheme.Hom.comp_preimage, hc, Scheme.Hom.comp_preimage]
  exact fun p hp => h hp

private theorem appSec_res_appSec_eq_of_comm_iso {Y Y' Z Z' : Scheme} {s : Z ⟶ Sp ℂ} {t : Y ⟶ Sp ℂ}
    {s' : Z' ⟶ Sp ℂ} {t' : Y' ⟶ Sp ℂ} (eY : Y ≅ Y') (eZ : Z ≅ Z') (c : Y ⟶ Z) (c' : Y' ⟶ Z')
    (hc : c ≫ eZ.hom = eY.hom ≫ c') (U' : Z'.Opens) (V' : Y'.Opens) (hV' : V' ≤ c' ⁻¹ᵁ U')
    (hV : eY.hom ⁻¹ᵁ V' ≤ c ⁻¹ᵁ eZ.hom ⁻¹ᵁ U') (τ : Sec s' U') :
    appSec t' t eY.hom V' (Sec.res t' hV' (appSec s' t' c' U' τ)) =
      Sec.res t hV (appSec s t c (eZ.hom ⁻¹ᵁ U') (appSec s' s eZ.hom U' τ)) := by
  have key : ∀ (g₁ g₂ : Y ⟶ Z') (_ : g₁ = g₂) (W : Y.Opens) (e₁ : W ≤ g₁ ⁻¹ᵁ U')
      (e₂ : W ≤ g₂ ⁻¹ᵁ U'), g₁.appLE U' W e₁ = g₂.appLE U' W e₂ := by
    rintro _ _ rfl _ _ _; rfl
  have e1 : eY.hom ⁻¹ᵁ V' ≤ (eY.hom ≫ c') ⁻¹ᵁ U' := by
    rw [Scheme.Hom.comp_preimage]; exact fun p hp => hV' hp
  have e2 : eY.hom ⁻¹ᵁ V' ≤ (c ≫ eZ.hom) ⁻¹ᵁ U' := by
    rw [Scheme.Hom.comp_preimage]; exact hV
  have L : appSec t' t eY.hom V' (Sec.res t' hV' (appSec s' t' c' U' τ)) =
      (eY.hom ≫ c').appLE U' _ e1 τ := by
    change eY.hom.app V' (Y'.presheaf.map (homOfLE hV').op (c'.app U' τ)) = _
    rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE]
    simp only [CommRingCat.comp_apply]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have R : Sec.res t hV (appSec s t c (eZ.hom ⁻¹ᵁ U') (appSec s' s eZ.hom U' τ)) =
      (c ≫ eZ.hom).appLE U' _ e2 τ := by
    change Y.presheaf.map (homOfLE hV).op (c.app _ (eZ.hom.app U' τ)) = _
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [L, R, key _ _ hc.symm]

theorem tanIso_of :
    UpperTheory.Gal.FixZ.TanIso := by
  intro Z Y Z' Y' s t s' t' eZ eY hs ht d c₁ c₂ c₁' c₂' h₁ h₂ h₁' h₂' hc₁ hc₂
  refine ⟨?E, ?_⟩
  case E =>
    unfold CxPts Points.PtsOver
    exact
      { toFun := fun x => ⟨x.1 ≫ eY.hom, by rw [Category.assoc, ht]; exact x.2⟩
        invFun := fun y => ⟨y.1 ≫ eY.inv, by rw [Category.assoc, ← ht, eY.inv_hom_id_assoc]; exact y.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
  refine ⟨fun x => rfl, fun x => ?_, fun x A hT => ?_⟩
  · change x.1 ≫ c₁ = x.1 ≫ c₂ ↔ (x.1 ≫ eY.hom) ≫ c₁' = (x.1 ≫ eY.hom) ≫ c₂'
    rw [Category.assoc, Category.assoc, ← hc₁, ← hc₂, ← Category.assoc, ← Category.assoc x.1,
      cancel_mono]
  · obtain ⟨U', V', hV1', hV2', τ, hx, hU', hV', φ', hsm, hd1, hd2, hker⟩ := hT
    set σ := secEquiv eY ht V' with hσ
    have hσa : ∀ g, σ g = appSec t' t eY.hom V' g := fun g => rfl
    have EV : ∀ g : Sec t' V', CxPts.ev t' (RingHom.id ℂ) V' g
        (⟨x.1 ≫ eY.hom, by rw [Category.assoc, ht]; exact x.2⟩ : CxPts t' (RingHom.id ℂ)) =
        CxPts.ev t (RingHom.id ℂ) (eY.hom ⁻¹ᵁ V') (σ g) x := fun g =>
      valR_comp_eq_valR_app x.1 eY.hom V' g
    obtain ⟨Ψ, hΨD, hΨs⟩ := exists_kaehler_equiv_D_of_algEquiv σ.symm
    have hW1 := preimage_le_preimage_preimage_of_comm_iso eY eZ c₁ c₁' hc₁ U' V' hV1'
    have hW2 := preimage_le_preimage_preimage_of_comm_iso eY eZ c₂ c₂' hc₂ U' V' hV2'
    have q1 : ∀ l, σ.symm (Sec.res t hW1 (appSec s t c₁ (eZ.hom ⁻¹ᵁ U')
        (appSec s' s eZ.hom U' (τ l)))) = Sec.res t' hV1' (appSec s' t' c₁' U' (τ l)) := fun l =>
      σ.injective (by rw [AlgEquiv.apply_symm_apply, hσa, appSec_res_appSec_eq_of_comm_iso eY eZ c₁ c₁' hc₁ U' V' hV1' hW1 (τ l)])
    have q2 : ∀ l, σ.symm (Sec.res t hW2 (appSec s t c₂ (eZ.hom ⁻¹ᵁ U')
        (appSec s' s eZ.hom U' (τ l)))) = Sec.res t' hV2' (appSec s' t' c₂' U' (τ l)) := fun l =>
      σ.injective (by rw [AlgEquiv.apply_symm_apply, hσa, appSec_res_appSec_eq_of_comm_iso eY eZ c₂ c₂' hc₂ U' V' hV2' hW2 (τ l)])
    refine ⟨eZ.hom ⁻¹ᵁ U', eY.hom ⁻¹ᵁ V', hW1, hW2, fun l => appSec s' s eZ.hom U' (τ l), hx,
      hU'.preimage_of_isIso eZ.hom, hV'.preimage_of_isIso eY.hom, φ' ∘ₗ Ψ.toLinearMap,
      ?_, ?_, ?_, ?_⟩
    · intro b ω
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΨs, hsm]
      erw [EV]
      rw [AlgEquiv.apply_symm_apply]
    · intro l
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΨD, q1]
      exact hd1 l
    · intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hΨD, q2]
      exact hd2 j
    · intro ω hω
      obtain ⟨m, b, ω', hb, hsum⟩ := hker (Ψ ω) hω
      refine ⟨m, fun i => σ (b i), fun i => Ψ.symm (ω' i), fun i => ?_, ?_⟩
      · rw [← EV]; exact hb i
      · apply Ψ.injective
        rw [hsum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hΨs, AlgEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

end UpperTheory.Gal.FixZ

end
