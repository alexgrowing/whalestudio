import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.VB

private theorem rk_cokernel {X : Scheme.{0}} {A E : X.Modules} {u : A ⟶ E} {a n : ℕ} (hu : IsSubbundle u)
    (hA : IsVB A a) (hE : IsVB E n) : IsVB (cokernel u) (n - a) := fun x => by
  have : Nonempty X := ⟨x⟩
  obtain ⟨_, s, hs⟩ := hu
  obtain rfl : n = a + s := hE.rank_unique (VBExt.isVB_and_cls_det_of_shortExact X (.mk u (cokernel.π _)
    (cokernel.condition _)) a s { exact := ShortComplex.exact_cokernel _ } hA hs).1
  rw [Nat.add_sub_cancel_left]
  exact hs x

open GlobalTheory.LineQuot in
theorem UpperTheory.vector_bundle_subbundle_universal :
    (∀ (B : Scheme.{0}) (E : B.Modules) (m r : ℕ), GlobalTheory.VB.IsVB E (m + r) →
          ∃ (G : Scheme.{0}) (γ : G ⟶ B) (P : G.Modules) (j : P ⟶ (Scheme.Modules.pullback γ).obj E),
            GlobalTheory.VB.IsVB P m ∧ Mono j ∧ GlobalTheory.VB.IsVB (Limits.cokernel j) r ∧
            ∀ (T : Scheme.{0}) (g : T ⟶ B) (P' : T.Modules) (j' : P' ⟶ (Scheme.Modules.pullback g).obj E),
              Mono j' → GlobalTheory.VB.IsVB (Limits.cokernel j') r →
              ∃! g' : T ⟶ G, ∃ w : g' ≫ γ = g, ∃ φ : (Scheme.Modules.pullback g').obj P ≅ P',
                φ.hom ≫ j' = (Scheme.Modules.pullback g').map j ≫ (Scheme.Modules.pullbackComp g' γ).hom.app E ≫
                  (Scheme.Modules.pullbackCongr w).hom.app E) →
        ∀ (B : Scheme.{0}) (E : B.Modules) (n m₁ m₂ : ℕ), GlobalTheory.VB.IsVB E n → m₁ ≤ m₂ → m₂ ≤ n →
        ∃ (G : Scheme.{0}) (γ : G ⟶ B) (S P : G.Modules) (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback γ).obj E),
          GlobalTheory.VB.IsVB S m₁ ∧ GlobalTheory.VB.IsVB P m₂ ∧ GlobalTheory.VB.IsSubbundle s ∧ GlobalTheory.VB.IsSubbundle j ∧
          GlobalTheory.VB.IsVB (Limits.cokernel j) (n - m₂) ∧ GlobalTheory.OmitFlag.IsPairBundle γ E m₁ m₂ s j := by
  intro H B E n m₁ m₂ hE h₁ h₂
  obtain ⟨G₂, γ₂, P₂, j₂, hP₂, hm₂, hc₂, U₂⟩ := H B E m₂ (n - m₂) (by rwa [Nat.add_sub_cancel' h₂])
  obtain ⟨G₁, γ₁, S, s, hS, hm₁, hc₁, U₁⟩ := H G₂ P₂ m₁ (m₂ - m₁) (by rwa [Nat.add_sub_cancel' h₁])
  have hsub := SubPull.isSubbundle_pullback _ _ γ₁ _ _ j₂ m₂ hP₂ ⟨hm₂, _, hc₂⟩
  have := hsub.mono
  have hcok : IsVB (cokernel ((Scheme.Modules.pullback γ₁).map j₂ ≫ (cmp γ₁ γ₂ rfl).hom.app E)) (n - m₂) :=
    ((hc₂.pullback γ₁).of_iso (PreservesCokernel.iso (Scheme.Modules.pullback γ₁) j₂)).of_iso
      (cokernelCompIsIso _ _).symm
  refine ⟨G₁, γ₁ ≫ γ₂, S, (Scheme.Modules.pullback γ₁).obj P₂, s,
    (Scheme.Modules.pullback γ₁).map j₂ ≫ (cmp γ₁ γ₂ rfl).hom.app E, hS, hP₂.pullback γ₁, ⟨hm₁, _, hc₁⟩,
    ⟨inferInstance, _, hcok⟩, hcok, ?_⟩
  intro T g S' P' s' j' hs' hj' hS' hP'
  have := hs'.mono
  have := hj'.mono
  have hB (g' : T ⟶ G₁) (g₂ : T ⟶ G₂) (w₂ : g' ≫ γ₁ = g₂) (w₁ : g₂ ≫ γ₂ = g) (w : g' ≫ γ₁ ≫ γ₂ = g) :
      (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback γ₁).map j₂ ≫ (cmp γ₁ γ₂ rfl).hom.app E) ≫
        (cmp g' (γ₁ ≫ γ₂) w).hom.app E = (cmp g' γ₁ w₂).hom.app P₂ ≫
            (Scheme.Modules.pullback g₂).map j₂ ≫ (cmp g₂ γ₂ w₁).hom.app E := by
    simp only [Functor.map_comp, Category.assoc]
    rw [cmp_assoc g' γ₁ γ₂ rfl w w₂ w₁, cmp_naturality_assoc]
  obtain ⟨g₂, ⟨w₁, φ₂, hφ₂⟩, hu₂⟩ := U₂ T g P' j' inferInstance (rk_cokernel hj' hP' (hE.pullback g))
  obtain ⟨g₁, ⟨w₂, φ₁, hφ₁⟩, hu₁⟩ := U₁ T g₂ S' (s' ≫ φ₂.inv) inferInstance
    ((rk_cokernel hs' hS' hP').of_iso (cokernelCompIsIso _ _).symm)
  rw [← cmp_hom_app] at hφ₁ hφ₂
  have w : g₁ ≫ γ₁ ≫ γ₂ = g := by rw [← Category.assoc, w₂, w₁]
  refine ⟨g₁, ⟨w, φ₁, (cmp g₁ γ₁ w₂).app P₂ ≪≫ φ₂, ?_, ?_⟩, ?_⟩
  · rw [← cmp_hom_app, hB g₁ g₂ w₂ w₁ w, ← hφ₂]
    simp
  · simp only [Iso.trans_hom, Iso.app_hom]
    rw [← reassoc_of% hφ₁]
    simp
  · rintro g' ⟨w', eS, eP, heP, heS⟩
    rw [← cmp_hom_app] at heP
    have w₂' : g' ≫ γ₁ = g₂ := by
      have w₁' := (Category.assoc ..).trans w'
      refine hu₂ _ ⟨w₁', ((cmp g' γ₁ rfl).app P₂).symm ≪≫ eP, ?_⟩
      rw [← cmp_hom_app, Iso.trans_hom, Category.assoc, heP, hB g' _ rfl w₁' w']
      simp
    refine hu₁ _ ⟨w₂', eS, ?_⟩
    have he : eP.hom = (cmp g' γ₁ w₂').hom.app P₂ ≫ φ₂.hom := by
      rw [← cancel_mono j', heP, hB g' _ w₂' w₁ w', Category.assoc, hφ₂]
    rw [← cmp_hom_app, reassoc_of% heS, he]
    simp
