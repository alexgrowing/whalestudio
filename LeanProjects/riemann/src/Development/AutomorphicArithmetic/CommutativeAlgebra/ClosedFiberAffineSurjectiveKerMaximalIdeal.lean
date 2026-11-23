import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

theorem UpperTheory.closed_fiber_affine_surjective_ker_maximalIdeal :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] {X F : Scheme.{0}} [IsAffine X] (p : X ⟶ Spec (CommRingCat.of A)) (r : F ⟶ X) (c : F ⟶ Spec (CommRingCat.of (ResidueField A))),
      IsPullback r c p (cpt A) → IsAffine F ∧ Function.Surjective r.appTop.hom ∧ RingHom.ker r.appTop.hom = (maximalIdeal A).map (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (p).appTop).hom) := by
  intro A _ _ X F _ p r c h
  have hcpt : IsClosedImmersion (cpt A) :=
    IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective)
  have hr : IsClosedImmersion r := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hcpt
  obtain ⟨hF, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine r
  refine ⟨hF, hsurj, ?_⟩
  have hinv : X.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    simp
  have key : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ r.appTop =
      CommRingCat.ofHom (residue A) ≫ (Scheme.ΓSpecIso _).inv ≫ c.appTop := by
    rw [← Scheme.Hom.comp_appTop, h.w, Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  set φ := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop).hom with hφ
  set I := (maximalIdeal A).map φ with hI
  apply le_antisymm
  · intro b hb
    rw [RingHom.mem_ker] at hb
    let π : Γ(X, ⊤) ⟶ CommRingCat.of (Γ(X, ⊤) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
    let χ0 : A ⧸ maximalIdeal A →+* Γ(X, ⊤) ⧸ I :=
      Ideal.Quotient.lift (maximalIdeal A) ((Ideal.Quotient.mk I).comp φ)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem φ ha))
    let χ : CommRingCat.of (ResidueField A) ⟶ CommRingCat.of (Γ(X, ⊤) ⧸ I) := CommRingCat.ofHom χ0
    let z : Spec (CommRingCat.of (Γ(X, ⊤) ⧸ I)) ⟶ X := Spec.map π ≫ X.isoSpec.inv
    have hz : z ≫ p = Spec.map χ ≫ cpt A := by
      apply ext_of_isAffine
      rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of A)).inv,
        ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) ⧸ I))).hom]
      simp only [z, cpt, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
        Scheme.ΓSpecIso_naturality_assoc, reassoc_of% hinv, Iso.inv_hom_id_assoc, Category.id_comp]
      ext a
      rfl
    let u := h.lift z (Spec.map χ) hz
    have hu : u ≫ r = z := h.lift_fst _ _ _
    have hzt : z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) ⧸ I))).hom = π := by
      simp only [z, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
        reassoc_of% hinv, Category.id_comp]
    have e1 : z.appTop = r.appTop ≫ u.appTop := by
      rw [← Scheme.Hom.comp_appTop, hu]
    have e2 := congrArg (fun f => f.hom b) hzt
    rw [e1] at e2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, hb, map_zero] at e2
    exact Ideal.Quotient.eq_zero_iff_mem.1 e2.symm
  · refine Ideal.map_le_iff_le_comap.2 (fun a ha => ?_)
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e := congrArg (fun f => f.hom a) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    rw [hφ, CommRingCat.hom_comp, RingHom.comp_apply, e, (IsLocalRing.residue_eq_zero_iff a).2 ha, map_zero, map_zero]

end
