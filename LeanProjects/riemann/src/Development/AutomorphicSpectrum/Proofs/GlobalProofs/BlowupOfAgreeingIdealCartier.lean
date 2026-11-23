import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsB

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue

theorem effCartier_of_forall_mem {X : Scheme.{0}} (I : X.IdealSheafData)
    (h : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ FinalTheorems.EffCartier (I.comap O.ι)) : FinalTheorems.EffCartier I := by
  intro x
  obtain ⟨O, hx, hO⟩ := h x
  obtain ⟨U, f, hxU, hf, hU⟩ := hO ⟨x, hx⟩
  have hV : IsAffineOpen (O.ι ''ᵁ U.1) := U.2.image_of_isOpenImmersion O.ι
  let e := (O.ι.appIso U.1).commRingCatIsoToRingEquiv
  refine ⟨⟨_, hV⟩, e.symm f, ⟨_, hxU, rfl⟩, ringEquiv_mem_nonZeroDivisors e.symm hf, ?_⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hU
  have hs : Function.Surjective ((O.ι.appIso U.1).inv.hom : _ →+* _) := e.symm.surjective
  have := Ideal.map_comap_of_surjective _ hs (I.ideal ⟨O.ι ''ᵁ U.1, hV⟩)
  rw [hU, Ideal.map_span, Set.image_singleton] at this
  exact this.symm

theorem isIso_restrict_of_effCartier {X X' : Scheme.{0}} {π : X' ⟶ X} {J : X.IdealSheafData} (h : FinalTheorems.Blowup π J)
    (U : X.Opens) (hU : FinalTheorems.EffCartier (J.comap U.ι)) : IsIso (π ∣_ U) := by
  obtain ⟨σ, hσ, -⟩ := h.2 U U.ι hU
  have pb := isPullback_morphismRestrict π U
  have hc : FinalTheorems.EffCartier (J.comap ((π ⁻¹ᵁ U).ι ≫ π)) := by
    rw [Scheme.IdealSheafData.comap_comp]; exact effCartier_comap_of_isOpenImmersion' _ _ h.1
  obtain ⟨τ, -, hτ⟩ := h.2 (π ⁻¹ᵁ U) ((π ⁻¹ᵁ U).ι ≫ π) hc
  have e : π ∣_ U ≫ σ = (π ⁻¹ᵁ U).ι :=
    (hτ _ (by simp [hσ])).trans (hτ _ rfl).symm
  exact ⟨pb.lift (𝟙 _) σ (by simp [hσ]), pb.hom_ext (by simp) (by simp [e]), by simp⟩

theorem eq_of_isIso_restrict {X X' T : Scheme.{0}} {π : X' ⟶ X} {O : X.Opens} [IsIso (π ∣_ O)] (s : T ⟶ X')
    (c : T ⟶ O) (h : c ≫ O.ι = s ≫ π) : s = c ≫ inv (π ∣_ O) ≫ (π ⁻¹ᵁ O).ι := by
  have pb := isPullback_morphismRestrict π O
  have h₁ : pb.lift c s h ≫ (π ∣_ O) = c := pb.lift_fst c s h
  have h₂ : pb.lift c s h ≫ (π ⁻¹ᵁ O).ι = s := pb.lift_snd c s h
  rw [← h₁, Category.assoc, IsIso.hom_inv_id_assoc, h₂]

theorem comap_eq_of_factor {T X : Scheme.{0}} {Z Z' : X.IdealSheafData} {O : X.Opens}
    (h : Z'.comap O.ι = Z.comap O.ι) (a : T ⟶ X) (b : T ⟶ O) (hab : b ≫ O.ι = a) : Z'.comap a = Z.comap a := by
  subst hab
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, h]

theorem exists_glue {W Y : Scheme.{0}} (W₁ W₂ : W.Opens) (h : W₁ ⊔ W₂ = ⊤) (σ₁ : W₁.toScheme ⟶ Y)
    (σ₂ : W₂.toScheme ⟶ Y)
    (hc : ∀ (T : Scheme.{0}) (a : T ⟶ W₁) (b : T ⟶ W₂) [IsOpenImmersion a], a ≫ W₁.ι = b ≫ W₂.ι →
      a ≫ σ₁ = b ≫ σ₂) :
    ∃ s : W ⟶ Y, W₁.ι ≫ s = σ₁ ∧ W₂.ι ≫ s = σ₂ := by
  let U : Bool → W.Opens := fun b => cond b W₁ W₂
  have hU : IsOpenCover U := by
    rw [IsOpenCover, eq_top_iff, ← h]
    exact sup_le (le_iSup U true) (le_iSup U false)
  let 𝒰 : W.OpenCover := W.openCoverOfIsOpenCover U hU
  let f : ∀ b : Bool, (U b).toScheme ⟶ Y := fun b => match b with
    | true => σ₁
    | false => σ₂
  haveI : ∀ b : Bool, IsOpenImmersion (𝒰.f b) := fun b => inferInstanceAs (IsOpenImmersion (U b).ι)
  have aux₁ : ∀ {A B C : Scheme.{0}} (p : A ⟶ C) (q : B ⟶ C), IsOpenImmersion q → IsOpenImmersion (pullback.fst p q) :=
    fun _ _ _ => inferInstance
  have aux₂ : ∀ {A B C : Scheme.{0}} (p : A ⟶ C) (q : B ⟶ C), IsOpenImmersion p → IsOpenImmersion (pullback.snd p q) :=
    fun _ _ _ => inferInstance
  have hf : ∀ x y : 𝒰.I₀, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ f y := by
    rintro (_ | _) (_ | _)
    · exact congrArg (· ≫ σ₂) ((cancel_mono (𝒰.f false)).1 pullback.condition)
    · exact (@hc _ (pullback.snd (𝒰.f false) (𝒰.f true)) (pullback.fst (𝒰.f false) (𝒰.f true))
        (aux₂ (𝒰.f false) (𝒰.f true) (this false)) pullback.condition.symm).symm
    · exact @hc _ (pullback.fst (𝒰.f true) (𝒰.f false)) (pullback.snd (𝒰.f true) (𝒰.f false))
        (aux₁ (𝒰.f true) (𝒰.f false) (this false)) pullback.condition
    · exact congrArg (· ≫ σ₁) ((cancel_mono (𝒰.f true)).1 pullback.condition)
  exact ⟨𝒰.glueMorphisms f hf, 𝒰.ι_glueMorphisms f hf true, 𝒰.ι_glueMorphisms f hf false⟩

theorem hom_ext_of_sup_eq_top {W Y : Scheme.{0}} (W₁ W₂ : W.Opens) (h : W₁ ⊔ W₂ = ⊤) (s t : W ⟶ Y)
    (h₁ : W₁.ι ≫ s = W₁.ι ≫ t) (h₂ : W₂.ι ≫ s = W₂.ι ≫ t) : s = t := by
  let U : Bool → W.Opens := fun b => cond b W₁ W₂
  have hU : IsOpenCover U := by
    rw [IsOpenCover, eq_top_iff, ← h]
    exact sup_le (le_iSup U true) (le_iSup U false)
  refine (W.openCoverOfIsOpenCover U hU).hom_ext _ _ ?_
  rintro (_ | _)
  · exact h₂
  · exact h₁

theorem blowup_of_eq_on_open : ∀ {X₁ X₂ : Scheme.{0}} (π : X₂ ⟶ X₁) (Z Z' : X₁.IdealSheafData) (O₁ O₂ : X₁.Opens),
    FinalTheorems.Blowup π Z → O₁ ⊔ O₂ = ⊤ → Z'.comap O₁.ι = Z.comap O₁.ι → (∀ x ∈ O₂, x ∉ Z'.support) →
    FinalTheorems.EffCartier (Z.comap O₂.ι) → FinalTheorems.Blowup π Z' := by
  intro X₁ X₂ π Z Z' O₁ O₂ hB hO h₁ h₂ hC
  have hiso := isIso_restrict_of_effCartier hB O₂ hC
  have cov : ∀ {W : Scheme.{0}} (g : W ⟶ X₁) (w : W), w ∈ g ⁻¹ᵁ O₁ ∨ w ∈ g ⁻¹ᵁ O₂ := by
    intro W g w
    have : g w ∈ O₁ ⊔ O₂ := by rw [hO]; trivial
    exact this
  have eq₁ : ∀ {W : Scheme.{0}} (g : W ⟶ X₁),
      Z'.comap ((g ⁻¹ᵁ O₁).ι ≫ g) = Z.comap ((g ⁻¹ᵁ O₁).ι ≫ g) := fun g =>
    comap_eq_of_factor h₁ _ (g ∣_ O₁) (morphismRestrict_ι g O₁)
  refine ⟨effCartier_of_forall_mem _ fun x => ?_, fun W g hg => ?_⟩
  · rcases cov π x with hx | hx
    · refine ⟨π ⁻¹ᵁ O₁, hx, ?_⟩
      rw [← Scheme.IdealSheafData.comap_comp, eq₁, Scheme.IdealSheafData.comap_comp]
      exact effCartier_comap_of_isOpenImmersion' _ _ hB.1
    · refine ⟨π ⁻¹ᵁ O₂, hx, ?_⟩
      rw [← Scheme.IdealSheafData.comap_comp]
      exact Principalise.effCartier_comap_of_disjoint _ _ fun w => h₂ _ w.2
  · have c₁ : FinalTheorems.EffCartier (Z.comap ((g ⁻¹ᵁ O₁).ι ≫ g)) := by
      rw [← eq₁, Scheme.IdealSheafData.comap_comp]
      exact effCartier_comap_of_isOpenImmersion' _ _ hg
    obtain ⟨σ₁, hσ₁, hu₁⟩ := hB.2 _ _ c₁
    have hσ₁' : σ₁ ≫ π = (g ⁻¹ᵁ O₁).ι ≫ g := hσ₁
    let σ₂ : (g ⁻¹ᵁ O₂).toScheme ⟶ X₂ := (g ∣_ O₂) ≫ inv (π ∣_ O₂) ≫ (π ⁻¹ᵁ O₂).ι
    have hσ₂ : σ₂ ≫ π = (g ⁻¹ᵁ O₂).ι ≫ g := by
      simp only [σ₂, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    have hW : g ⁻¹ᵁ O₁ ⊔ g ⁻¹ᵁ O₂ = ⊤ := eq_top_iff.2 fun w _ => cov g w
    obtain ⟨s, hs₁, hs₂⟩ := exists_glue (g ⁻¹ᵁ O₁) (g ⁻¹ᵁ O₂) hW σ₁ σ₂ (by
      intro T a b _ hab
      have hc : FinalTheorems.EffCartier (Z.comap (a ≫ (g ⁻¹ᵁ O₁).ι ≫ g)) := by
        rw [Scheme.IdealSheafData.comap_comp]
        exact effCartier_comap_of_isOpenImmersion' _ _ c₁
      obtain ⟨_, -, hu⟩ := hB.2 _ _ hc
      refine (hu _ (by beta_reduce; rw [Category.assoc, hσ₁'])).trans (hu _ ?_).symm
      beta_reduce
      rw [Category.assoc, hσ₂, ← Category.assoc, ← hab, Category.assoc])
    refine ⟨s, ?_, fun t ht => ?_⟩
    · refine hom_ext_of_sup_eq_top _ _ hW _ _ ?_ ?_
      · rw [← Category.assoc, hs₁, hσ₁']
      · rw [← Category.assoc, hs₂, hσ₂]
    · have ht' : t ≫ π = g := ht
      refine hom_ext_of_sup_eq_top _ _ hW _ _ ?_ ?_
      · rw [hs₁]; exact hu₁ _ (by beta_reduce; rw [Category.assoc, ht'])
      · rw [hs₂]
        exact eq_of_isIso_restrict _ (g ∣_ O₂) (by rw [morphismRestrict_ι, Category.assoc, ht'])

end GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
