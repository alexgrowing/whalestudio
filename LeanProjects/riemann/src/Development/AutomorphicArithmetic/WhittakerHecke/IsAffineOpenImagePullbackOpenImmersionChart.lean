import Mathlib

open CategoryTheory Limits AlgebraicGeometry TensorProduct

private lemma chart_open {X W E : Scheme.{0}} (π : W ⟶ X) (N : X.Opens) (hN : IsAffineOpen N)
    {S C T : CommRingCat.{0}} (φ : S ⟶ Γ(X, N)) (τ : E ⟶ Spec S)
    (q : (π ⁻¹ᵁ N).toScheme ⟶ E)
    (hq : IsPullback q (π ∣_ N) τ (hN.isoSpec.hom ≫ Spec.map φ))
    (χ : S ⟶ C) (c : Spec C ⟶ E) [IsOpenImmersion c] (hc : c ≫ τ = Spec.map χ)
    (l : Γ(X, N) ⟶ T) (r : C ⟶ T) (hpo : IsPushout φ χ l r) :
    ∃ (ι' : Spec T ⟶ (π ⁻¹ᵁ N).toScheme) (_ : IsOpenImmersion ι'),
      ι'.opensRange = q ⁻¹ᵁ c.opensRange ∧ ι' ≫ q = Spec.map r ≫ c ∧
      ι' ≫ (π ∣_ N) = Spec.map l ≫ hN.isoSpec.inv := by
  have L := IsPullback.of_hasPullback q c
  have big := L.paste_horiz hq.flip
  rw [hc] at big
  have hS := isPullback_SpecMap_of_isPushout φ χ l r hpo
  have sq : IsPullback hN.isoSpec.inv (Spec.map φ) (hN.isoSpec.hom ≫ Spec.map φ) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hS' := hS.paste_horiz sq
  rw [Category.comp_id] at hS'
  let e := IsPullback.isoIsPullback _ _ hS' big
  refine ⟨e.hom ≫ pullback.fst q c, inferInstance, ?_, ?_, ?_⟩
  · rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc,
      IsPullback.isoIsPullback_hom_snd]
  · rw [Category.assoc, IsPullback.isoIsPullback_hom_fst]

private lemma chart_ring {X W : Scheme.{0}} (π : W ⟶ X) (N : X.Opens) (hN : IsAffineOpen N)
    {S C T : CommRingCat.{0}} (φ : S ⟶ Γ(X, N)) (χ : S ⟶ C)
    (l : Γ(X, N) ⟶ T) (r : C ⟶ T) (hpo : IsPushout φ χ l r)
    (ι : Spec T ⟶ W) [IsOpenImmersion ι] (hι : ι ≫ π = Spec.map l ≫ hN.fromSpec)
    (V : W.Opens) (hV : V = ι ''ᵁ ⊤) (hle : V ≤ π ⁻¹ᵁ N) :
    ∃ ρ : C ⟶ Γ(W, V), IsPushout φ χ (π.appLE N V hle) ρ ∧
      ∀ f : C, ι ''ᵁ (PrimeSpectrum.basicOpen (r.hom f)) = W.basicOpen (ρ.hom f) := by
  subst hV
  have hVa : IsAffineOpen (ι ''ᵁ ⊤) := (isAffineOpen_top (Spec T)).image_of_isOpenImmersion ι
  let θ : Γ(W, ι ''ᵁ ⊤) ≅ T := ι.appIso ⊤ ≪≫ Scheme.ΓSpecIso T
  have key1 : Spec.map θ.hom ≫ hVa.fromSpec = ι := by
    have h0 := IsAffineOpen.SpecMap_appLE_fromSpec ι hVa (isAffineOpen_top (Spec T))
      (ι.preimage_image_eq ⊤).ge
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h0
    simp only [θ, Iso.trans_hom, Spec.map_comp, Category.assoc, Scheme.Hom.appIso_hom']
    rw [h0, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
  have key2 : π.appLE N (ι ''ᵁ ⊤) hle ≫ θ.hom = l := by
    apply Spec.map_injective
    rw [← cancel_mono hN.fromSpec, Spec.map_comp, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec π hN hVa hle, ← Category.assoc, key1, hι]
  refine ⟨r ≫ θ.inv, ?_, ?_⟩
  · refine hpo.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) θ.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · rw [← key2]
      simp
    · simp
  · intro f
    rw [← basicOpen_eq_of_affine, Scheme.image_basicOpen]
    rfl

theorem UpperTheory.isAffineOpen_image_pullback_openImmersion_chart :
    ∀ {S C : Type} [CommRing S] [CommRing C] {X W E : Scheme.{0}} (π : W ⟶ X) (N : X.Opens)
        (hN : IsAffineOpen N) (φ : S →+* Γ(X, N)) (τ : E ⟶ Spec (CommRingCat.of S))
        (q : (π ⁻¹ᵁ N).toScheme ⟶ E)
        (_ : IsPullback q (π ∣_ N) τ (hN.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ)))
        (χ : S →+* C) (c : Spec (CommRingCat.of C) ⟶ E) [IsOpenImmersion c]
        (_ : c ≫ τ = Spec.map (CommRingCat.ofHom χ)),
        IsAffineOpen ((π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ c.opensRange)) ∧
        ∃ (hle : (π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ c.opensRange) ≤ π ⁻¹ᵁ N)
          (ρ : C →+* Γ(W, (π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ c.opensRange))),
          IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom χ) (Scheme.Hom.appLE π N _ hle) (CommRingCat.ofHom ρ) ∧
          ∀ (O : E.Opens) (f : C), c ⁻¹ᵁ O = PrimeSpectrum.basicOpen f →
            (π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ c.opensRange) ⊓ (π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ O) = W.basicOpen (ρ f) := by
  intro S C _ _ X W E π N hN φ τ q hq χ c _ hc
  obtain ⟨ι', _, hr, hq', hπ'⟩ := chart_open π N hN (CommRingCat.ofHom φ) τ q hq (CommRingCat.ofHom χ) c hc
    (pushout.inl (CommRingCat.ofHom φ) (CommRingCat.ofHom χ))
    (pushout.inr (CommRingCat.ofHom φ) (CommRingCat.ofHom χ)) (IsPushout.of_hasPushout _ _)
  have hι : (ι' ≫ (π ⁻¹ᵁ N).ι) ≫ π =
      Spec.map (pushout.inl (CommRingCat.ofHom φ) (CommRingCat.ofHom χ)) ≫ hN.fromSpec := by
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hπ', Category.assoc]
    rfl
  have hV : (π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ c.opensRange) = (ι' ≫ (π ⁻¹ᵁ N).ι) ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp, hr]
  have hle : (π ⁻¹ᵁ N).ι ''ᵁ (q ⁻¹ᵁ c.opensRange) ≤ π ⁻¹ᵁ N := (π ⁻¹ᵁ N).ι_image_le _
  obtain ⟨ρ, hpo, hb⟩ := chart_ring π N hN (CommRingCat.ofHom φ) (CommRingCat.ofHom χ) _ _
    (IsPushout.of_hasPushout _ _) (ι' ≫ (π ⁻¹ᵁ N).ι) hι _ hV hle
  refine ⟨?_, hle, ρ.hom, ?_, ?_⟩
  · rw [hV]
    exact (isAffineOpen_top _).image_of_isOpenImmersion _
  · simpa using hpo
  · intro O f hO
    have hbo : (PrimeSpectrum.basicOpen ((pushout.inr (CommRingCat.ofHom φ) (CommRingCat.ofHom χ)).hom f) :
        (Spec _).Opens) = ι' ⁻¹ᵁ q ⁻¹ᵁ O := by
      rw [← Scheme.Hom.comp_preimage, hq', Scheme.Hom.comp_preimage, hO]
      ext x
      exact Iff.rfl
    rw [← hb f, hbo]
    have hinj := (π ⁻¹ᵁ N).ι.isOpenEmbedding.injective
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_image, Scheme.Hom.coe_image, Scheme.Hom.coe_image, ← hr,
      ← Set.image_inter hinj, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
    congr 1
    rw [← Scheme.Hom.coe_image, Scheme.Hom.image_preimage_eq_opensRange_inf]
    rfl
