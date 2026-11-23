import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsFlatBaseChangeAffineMilnorSquareOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchExistsExtendBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsOfSchemeOverArtinianFibreProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeHomExtOfJointlyInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointCoverSectionDetectRestrictOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedCoverAffineNbhdMapsIntoAffineStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.FlatPinch

theorem surjective_fst_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (hP : IsPullback f₁ f₂ g₁ g₂) (hg₂ : Function.Surjective g₂) :
    Function.Surjective f₁ := by
  intro r
  obtain ⟨s, hs⟩ := hg₂ (g₁ r)
  obtain ⟨a, ha, -⟩ := (GlobalTheory.DualOpen.elem_of_isPullback_ring hP).2 r s hs.symm
  exact ⟨a, ha⟩

end GlobalTheory.FlatPinch

namespace GlobalTheory.FlatPinch

theorem resLE_homOfLE {Y' T X : Scheme.{0}} (f' : Y' ⟶ T) {V V' : T.Opens} (h : V' ≤ V) (g : V.toScheme ⟶ X)
    (w : Y' ⟶ X) (hg : f'.resLE V _ le_rfl ≫ g = (f' ⁻¹ᵁ V).ι ≫ w) :
    f'.resLE V' _ le_rfl ≫ T.homOfLE h ≫ g = (f' ⁻¹ᵁ V').ι ≫ w := by
  have e : f'.resLE V' _ le_rfl ≫ T.homOfLE h = Y'.homOfLE (f'.preimage_mono h) ≫ f'.resLE V _ le_rfl := by
    rw [← cancel_mono V.ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]
  rw [reassoc_of% e, hg, Scheme.homOfLE_ι_assoc]

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), Flat Y.hom → IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) → IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ Y₂.hom = Y₀.hom ≫ Spec.map g₂ → IsPushout i₁ i₂ j₁ j₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₁ hg₂ Y Y₁ Y₂ Y₀ j₁ j₂ i₁ i₂ hfl h₁ h₂ h₀ hij hp₂
  have hf₁ : Function.Surjective f₁ := surjective_fst_of_isPullback hP hg₂
  have hf₂ : Function.Surjective f₂ := surjective_fst_of_isPullback hP.flip hg₁
  haveI : IsClosedImmersion j₁ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₁.flip (IsClosedImmersion.spec_of_surjective f₁ hf₁)
  haveI : IsClosedImmersion j₂ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₂.flip (IsClosedImmersion.spec_of_surjective f₂ hf₂)
  obtain ⟨hcov, hpts⟩ := GlobalTheory.T.points_of_scheme_over_artinian_fibre_product _ _ _ _ _ _ _ _ hP hloc hart hg₁ hg₂ _ _ _ _ Y.hom Y₁.hom Y₂.hom Y₀.hom
    j₁ j₂ i₁ i₂ h₁ h₂ h₀ hij
  have hM : GlobalTheory.DualOpen.Milnor (Spec.map f₂) (Spec.map f₁) (Spec.map g₂) (Spec.map g₁) :=
    GlobalTheory.DualOpen.Milnor.of_isPullback hP.flip hg₁
  haveI : Flat Y.hom := hfl
  have SEC := fun W => GlobalTheory.DualOpen.sections_of_squares hM h₂ h₁ h₀ hij.symm hp₂ W
  have hinj : ∀ (W : Y.left.Opens) (a b : Γ(Y.left, W)), j₁.app W a = j₁.app W b → j₂.app W a = j₂.app W b → a = b :=
    fun W a b e1 e2 => (SEC W).1 a b e2 e1
  have uniqV := fun (X : Scheme.{0}) (V : Y.left.Opens) =>
    GlobalTheory.T.scheme_hom_ext_of_jointly_surjective_of_app_injective _ _ _ X _ _ ((GlobalTheory.T.jointCover_sectionDetect_restrict_open _ _ _ j₁ j₂ hcov hinj V).1)
      ((GlobalTheory.T.jointCover_sectionDetect_restrict_open _ _ _ j₁ j₂ hcov hinj V).2)
  have uniq : ∀ (X : Scheme.{0}) (a b : Y.left ⟶ X), j₁ ≫ a = j₁ ≫ b → j₂ ≫ a = j₂ ≫ b → a = b :=
    fun X => GlobalTheory.T.scheme_hom_ext_of_jointly_surjective_of_app_injective _ _ _ X j₁ j₂ hcov hinj
  have key : ∀ (X : Scheme.{0}) (a₁ : Y₁.left ⟶ X) (a₂ : Y₂.left ⟶ X), i₁ ≫ a₁ = i₂ ≫ a₂ →
      ∃ a : Y.left ⟶ X, j₁ ≫ a = a₁ ∧ j₂ ≫ a = a₂ := by
    intro X a₁ a₂ ha
    have hpa : ∀ (y₁ : Y₁.left) (y₂ : Y₂.left), j₁ y₁ = j₂ y₂ → a₁ y₁ = a₂ y₂ := by
      intro y₁ y₂ h
      obtain ⟨y₀, rfl, rfl⟩ := hpts y₁ y₂ h
      have := congrArg (fun q : Y₀.left ⟶ X => q y₀) ha
      simpa using this
    have hloc := GlobalTheory.T.exists_affine_nbhd_preimage_le_of_closed_cover _ _ _ X j₁ j₂ a₁ a₂ hcov hpa
    let Idx := {p : Y.left.Opens × X.affineOpens //
      IsAffineOpen p.1 ∧ j₁ ⁻¹ᵁ p.1 ≤ a₁ ⁻¹ᵁ p.2.1 ∧ j₂ ⁻¹ᵁ p.1 ≤ a₂ ⁻¹ᵁ p.2.1}
    have hcovI : TopologicalSpace.IsOpenCover (fun p : Idx => p.1.1) := by
      rw [TopologicalSpace.IsOpenCover, eq_top_iff]
      intro y _
      obtain ⟨W, U, hW, hy, h1, h2⟩ := hloc y
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(W, U), hW, h1, h2⟩, hy⟩
    have EO : ∀ p : Idx, ∃ g : p.1.1.toScheme ⟶ X, j₁.resLE _ _ le_rfl ≫ g = (j₁ ⁻¹ᵁ p.1.1).ι ≫ a₁ ∧
        j₂.resLE _ _ le_rfl ≫ g = (j₂ ⁻¹ᵁ p.1.1).ι ≫ a₂ := by
      rintro ⟨⟨W, U⟩, hW, hx, hz⟩
      have hW1 : IsAffineOpen (j₁ ⁻¹ᵁ W) := hW.preimage j₁
      have hW2 : IsAffineOpen (j₂ ⁻¹ᵁ W) := hW.preimage j₂
      have hpre : i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W) = i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ W) := by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hij]
      refine GlobalTheory.Pinch.exists_glue_of_sections j₁ j₂ W hW hW1 hW2 U a₁ a₂ hx hz ?_ ?_
      · intro t₁ t₂ e1 e2
        rw [← Scheme.Hom.app_eq_appLE] at e1 e2
        exact hinj W t₁ t₂ e1 e2
      · intro u
        obtain ⟨t, ht2, ht1⟩ := (SEC W).2 (i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W)) le_rfl hpre.le le_rfl
          (a₂.appLE U.1 _ hz u) (a₁.appLE U.1 _ hx u) (by
            have e1 := Scheme.Hom.appLE_comp_appLE i₂ a₂ U.1 _ (i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W)) hz le_rfl
            have e2 := Scheme.Hom.appLE_comp_appLE i₁ a₁ U.1 _ (i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W)) hx hpre.le
            have e3 := GlobalTheory.Pinch.appLE_congr_hom ha.symm U.1 (i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W))
              (fun w hw => hz hw) (fun w hw => hx (hpre.le hw))
            have := congrArg (fun q => q.hom u) (e1.trans (e3.trans e2.symm))
            simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
            exact this)
        refine ⟨t, ?_, ?_⟩
        · rw [← Scheme.Hom.app_eq_appLE]; exact ht1
        · rw [← Scheme.Hom.app_eq_appLE]; exact ht2
    let 𝒰 := Y.left.openCoverOfIsOpenCover _ hcovI
    choose g hg using EO
    have hc : ∀ a b : Idx, pullback.fst (𝒰.f a) (𝒰.f b) ≫ g a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ g b := by
      intro a b
      have hPb := isPullback_opens_inf a.1.1 b.1.1
      change pullback.fst a.1.1.ι b.1.1.ι ≫ g a = pullback.snd a.1.1.ι b.1.1.ι ≫ g b
      rw [← cancel_epi hPb.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc]
      refine uniqV X (a.1.1 ⊓ b.1.1) _ _ ?_ ?_
      · rw [resLE_homOfLE j₁ _ _ a₁ (hg a).1, resLE_homOfLE j₁ _ _ a₁ (hg b).1]
      · rw [resLE_homOfLE j₂ _ _ a₂ (hg a).2, resLE_homOfLE j₂ _ _ a₂ (hg b).2]
    let z₀ := 𝒰.glueMorphisms g hc
    have hz₀ : ∀ a : Idx, a.1.1.ι ≫ z₀ = g a := fun a => 𝒰.ι_glueMorphisms g hc a
    refine ⟨z₀, ?_, ?_⟩
    · have hcov1 : TopologicalSpace.IsOpenCover (fun p : Idx => j₁ ⁻¹ᵁ p.1.1) := by
        rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcovI, Scheme.Hom.preimage_top]
      refine Scheme.Cover.hom_ext (Y₁.left.openCoverOfIsOpenCover _ hcov1) _ _ fun a => ?_
      change (j₁ ⁻¹ᵁ a.1.1).ι ≫ j₁ ≫ z₀ = (j₁ ⁻¹ᵁ a.1.1).ι ≫ a₁
      rw [← (hg a).1, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι j₁ (le_rfl), Category.assoc]
    · have hcov2 : TopologicalSpace.IsOpenCover (fun p : Idx => j₂ ⁻¹ᵁ p.1.1) := by
        rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcovI, Scheme.Hom.preimage_top]
      refine Scheme.Cover.hom_ext (Y₂.left.openCoverOfIsOpenCover _ hcov2) _ _ fun a => ?_
      change (j₂ ⁻¹ᵁ a.1.1).ι ≫ j₂ ≫ z₀ = (j₂ ⁻¹ᵁ a.1.1).ι ≫ a₂
      rw [← (hg a).2, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι j₂ (le_rfl), Category.assoc]
  refine IsPushout.of_isColimit (c := PushoutCocone.mk j₁ j₂ hij)
    (PushoutCocone.IsColimit.mk _ (fun s => Classical.choose (key _ s.inl s.inr s.condition))
      (fun s => (Classical.choose_spec (key _ s.inl s.inr s.condition)).1)
      (fun s => (Classical.choose_spec (key _ s.inl s.inr s.condition)).2)
      (fun s m e1 e2 => uniq _ _ _ (e1.trans (Classical.choose_spec (key _ s.inl s.inr s.condition)).1.symm)
        (e2.trans (Classical.choose_spec (key _ s.inl s.inr s.condition)).2.symm)))

end GlobalTheory.FlatPinch
