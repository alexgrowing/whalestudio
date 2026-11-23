import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutAppLEOfIsPullbackOfIsAffine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.PushoutSquare

theorem isPullback_of_forall_isPushout_app :
    ∀ (X Y S S' : Scheme.{0}) (j : X ⟶ Y) (p : X ⟶ S') (y : Y ⟶ S) (q : S' ⟶ S), IsAffine S → IsAffine S' → IsAffineHom j → j ≫ y = p ≫ q → (∀ V : Y.Opens, IsAffineOpen V → IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) q.appTop (j.app V) (p.appLE ⊤ (j ⁻¹ᵁ V) (fun _ _ => trivial))) → IsPullback j p y q := by
  intro X Y S S' j p y q hS hS' hj w H
  let φ : X ⟶ pullback y q := pullback.lift j p w
  have hφ1 : φ ≫ pullback.fst y q = j := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ pullback.snd y q = p := pullback.lift_snd _ _ _
  suffices hiso : IsIso φ by
    exact IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ1 hφ2
  have hPb : IsPullback (pullback.fst y q) (pullback.snd y q) y q := IsPullback.of_hasPullback y q
  haveI : IsAffineHom q := inferInstance
  haveI : IsAffineHom (pullback.fst y q) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback hPb.flip inferInstance
  let U : Y.affineOpens → (pullback y q).Opens := fun V => pullback.fst y q ⁻¹ᵁ V.1
  have hU : ⨆ V, U V = ⊤ := by
    show ⨆ V : Y.affineOpens, pullback.fst y q ⁻¹ᵁ (V : Y.Opens) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  show MorphismProperty.isomorphisms Scheme φ
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hU]
  intro V
  have hpre : φ ⁻¹ᵁ U V = j ⁻¹ᵁ V.1 := by
    show φ ⁻¹ᵁ (pullback.fst y q ⁻¹ᵁ V.1) = j ⁻¹ᵁ V.1
    rw [← Scheme.Hom.comp_preimage, hφ1]
  have hUa : IsAffineOpen (U V) := V.2.preimage _
  have hSa : IsAffineOpen (φ ⁻¹ᵁ U V) := by rw [hpre]; exact V.2.preimage j
  haveI : IsAffine (U V).toScheme := hUa
  haveI : IsAffine (φ ⁻¹ᵁ U V).toScheme := hSa

  have P1 := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine Y (pullback y q) S S'
    (pullback.fst y q) (pullback.snd y q) y q hPb hS hS' V.1 V.2
  have P2 := H V.1 V.2
  let c : Γ(pullback y q, U V) ⟶ Γ(X, j ⁻¹ᵁ V.1) := φ.appLE (U V) (j ⁻¹ᵁ V.1) hpre.ge
  have key : ∀ {T : Scheme.{0}} (g j' : X ⟶ T) (hg : g = j') (A : T.Opens) (e : j' ⁻¹ᵁ A ≤ g ⁻¹ᵁ A),
      g.appLE A (j' ⁻¹ᵁ A) e = j'.appLE A (j' ⁻¹ᵁ A) le_rfl := by
    intro T g j' hg A e; subst hg; rfl
  have hc1 : (pullback.fst y q).app V.1 ≫ c = j.app V.1 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]
    exact key _ _ hφ1 _ _
  have hc2 : (pullback.snd y q).appLE ⊤ (pullback.fst y q ⁻¹ᵁ V.1) (fun _ _ => trivial) ≫ c =
      p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
    refine (Scheme.Hom.appLE_comp_appLE φ (pullback.snd y q) ⊤ (pullback.fst y q ⁻¹ᵁ V.1) (j ⁻¹ᵁ V.1)
      (fun _ _ => trivial) hpre.ge).trans ?_
    have e2 : ∀ (e : j ⁻¹ᵁ V.1 ≤ (φ ≫ pullback.snd y q) ⁻¹ᵁ ⊤),
        (φ ≫ pullback.snd y q).appLE ⊤ (j ⁻¹ᵁ V.1) e = p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
      intro e
      have gen : ∀ (g : X ⟶ S') (hg : g = p) (e' : j ⁻¹ᵁ V.1 ≤ g ⁻¹ᵁ ⊤),
          g.appLE ⊤ (j ⁻¹ᵁ V.1) e' = p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
        intro g hg e'; subst hg; rfl
      exact gen _ hφ2 e
    exact e2 _
  have hcE : c = (P1.isoIsPushout _ _ P2).hom := by
    apply P1.hom_ext
    · rw [IsPushout.inl_isoIsPushout_hom]; exact hc1
    · rw [IsPushout.inr_isoIsPushout_hom]; exact hc2
  have hcI : IsIso c := by rw [hcE]; infer_instance
  have hTop : IsIso (φ ∣_ U V).appTop := by
    rw [Scheme.Hom.appTop, morphismRestrict_app']
    refine (Scheme.Hom.appLE_congr φ _ (Scheme.Opens.ι_image_top (U V))
      ((Scheme.Opens.ι_image_top (φ ⁻¹ᵁ U V)).trans hpre) (fun f => IsIso f)).mpr ?_
    exact hcI
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _)
    (arrowIsoSpecΓOfIsAffine (φ ∣_ U V))).mpr (inferInstanceAs (IsIso (Spec.map _)))

end GlobalTheory.PushoutSquare
