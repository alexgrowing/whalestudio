import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitDesc

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3 MorphismProperty
universe u v

set_option backward.isDefEq.respectTransparency.types false in
private theorem isProper_desc {A G U Z : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Flat j] [Surjective j] [QuasiCompact j] (h : IsPullback φ f g j) [IsProper f] : IsProper g := by
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hUC : UniversallyClosed g :=
    of_isPullback_of_descendsAlong h.flip hQ (inferInstanceAs (UniversallyClosed f))
  have hLFT : LocallyOfFiniteType g :=
    of_isPullback_of_descendsAlong h.flip hQ (inferInstanceAs (LocallyOfFiniteType f))
  have hD : MorphismProperty.diagonal @UniversallyClosed g := by
    refine of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) h.flip hQ ?_
    rw [MorphismProperty.diagonal_iff]
    infer_instance
  rw [MorphismProperty.diagonal_iff] at hD
  have hP : IsProper (pullback.diagonal g) := IsProper.mk
  have hC : IsClosedImmersion (pullback.diagonal g) :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨hP, inferInstance⟩
  haveI : IsSeparated g := ⟨hC⟩
  exact IsProper.mk

set_option backward.isDefEq.respectTransparency.types false in
private theorem isFinite_desc_fin (W : Scheme.{0}) (n : ℕ) :
    IsFinite (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
  induction n with
  | zero =>
    haveI := Function.isEmpty (sigmaMk (fun _ : Fin 0 => W)).symm
    infer_instance
  | succ n ih =>
    let t := extendCofanIsColimit (fun _ : Fin (n + 1) => W) (coproductIsCoproduct fun _ : Fin n => W)
      (coprodIsCoprod W (∐ fun _ : Fin n => W))
    let e : (∐ fun _ : Fin (n + 1) => W) ≅ W ⨿ (∐ fun _ : Fin n => W) :=
      (coproductIsCoproduct fun _ : Fin (n + 1) => W).coconePointUniqueUpToIso t
    have key : (Sigma.desc (f := fun _ : Fin (n + 1) => W) fun _ => 𝟙 W) =
        e.hom ≫ coprod.desc (𝟙 W) (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
      refine Sigma.hom_ext _ _ fun j => ?_
      have hj := IsColimit.comp_coconePointUniqueUpToIso_hom
        (coproductIsCoproduct (fun _ : Fin (n + 1) => W)) t ⟨j⟩
      rw [Sigma.ι_desc, ← Category.assoc]
      erw [hj]
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [extendCofan, Cofan.mk_ι_app, Fin.cases_zero]
        exact (coprod.inl_desc _ _).symm
      · simp only [extendCofan, Cofan.mk_ι_app, Fin.cases_succ]
        show 𝟙 W = (Sigma.ι (fun _ : Fin n => W) i ≫ coprod.inr) ≫
          coprod.desc (𝟙 W) (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W)
        rw [Category.assoc, coprod.inr_desc, Sigma.ι_desc]
    rw [key]
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
private theorem isFinite_desc (W : Scheme.{0}) (J : Type) [Finite J] :
    IsFinite (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have key : (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) =
      (Sigma.reindex e.symm (fun _ : J => W)).inv ≫ (Sigma.desc (f := fun _ : Fin n => W) fun _ => 𝟙 W) := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc, ← Category.assoc]
    have h := Sigma.ι_reindex_inv e.symm (fun _ : J => W) (e j)
    simp only [Equiv.symm_apply_apply] at h
    rw [h]
    exact (Sigma.ι_desc (f := fun _ : Fin n => W) (fun _ => 𝟙 W) (e j)).symm
  rw [key]
  haveI := isFinite_desc_fin W n
  infer_instance

private theorem locallyQuasiFinite_of_etale {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f := by
  have hf : affineLocally RingHom.Etale f := by
    rw [← HasRingHomProperty.eq_affineLocally @Etale]
    exact ‹Etale f›
  rw [HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]
  refine affineLocally_le (fun {R S} _ _ {g} hg => ?_) f hf
  letI : Algebra R S := RingHom.toAlgebra g
  have : Algebra.Etale R S := hg
  show Algebra.QuasiFinite R S
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
theorem UpperTheory.Gal.G3.jSplitDesc :
    SplitDesc := by
  intro Z Y W s c _ _ _ J _ σ hs
  obtain ⟨hσ, hiso⟩ := hs
  haveI : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have key : pullback.snd s c =
      inv (Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hσ j, Category.id_comp])) ≫
        Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W := by
    rw [IsIso.eq_inv_comp]
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc_assoc, pullback.lift_snd, Sigma.ι_desc]
  haveI : IsFinite (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) := isFinite_desc W J
  haveI : Etale (Sigma.desc (f := fun _ : J => W) fun _ => 𝟙 W) :=
    IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  haveI : IsFinite (pullback.snd s c) := by rw [key]; infer_instance
  haveI : Etale (pullback.snd s c) := by rw [key]; infer_instance
  have hpb := IsPullback.of_hasPullback s c
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) c :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  haveI : IsProper s := isProper_desc hpb
  have hE : Etale s := of_isPullback_of_descendsAlong hpb.flip hQ (inferInstanceAs (Etale (pullback.snd s c)))
  haveI := hE
  haveI := locallyQuasiFinite_of_etale s
  exact ⟨(IsFinite.iff_isProper_and_locallyQuasiFinite s).mpr ⟨inferInstance, inferInstance⟩, hE⟩
