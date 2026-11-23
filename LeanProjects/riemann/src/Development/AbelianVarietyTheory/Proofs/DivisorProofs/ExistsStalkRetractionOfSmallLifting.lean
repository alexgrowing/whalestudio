import Mathlib

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.SmallLift

theorem map_closedPoint {X : Scheme.{0}} {x : X} {R : CommRingCat.{0}} [IsLocalRing R]
    (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (closedPoint R) = x := by
  refine (Scheme.Hom.comp_apply (Spec.map φ) (X.fromSpecStalk x) (closedPoint R)).trans ?_
  exact (congrArg (X.fromSpecStalk x) (Spec_closedPoint (f := φ))).trans
    Scheme.fromSpecStalk_closedPoint

theorem step {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) (C : Type) [CommRing C] [IsLocalRing C]
    (I : Ideal C) [IsLocalRing (C ⧸ I)]
    (H : ∀ (a : Spec (CommRingCat.of (C ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of C) ⟶ Y),
      a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b →
      ∃ l : Spec (CommRingCat.of C) ⟶ X,
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b)
    (π : Y.presheaf.stalk (f x) ⟶ CommRingCat.of C)
    (ψ : X.presheaf.stalk x ⟶ CommRingCat.of (C ⧸ I)) [IsLocalHom ψ.hom]
    (hψ : ψ.hom.comp (f.stalkMap x).hom = (Ideal.Quotient.mk I).comp π.hom) :
    ∃ g : X.presheaf.stalk x →+* C, IsLocalHom g ∧ g.comp (f.stalkMap x).hom = π.hom := by
  have e : f.stalkMap x ≫ ψ =
      π ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    ext1
    exact hψ
  obtain ⟨l, hl, hs⟩ := H (Spec.map ψ ≫ X.fromSpecStalk x)
    (Spec.map π ≫ Y.fromSpecStalk (f x)) (by
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc,
        ← Spec.map_comp_assoc, e])
  obtain ⟨⟨x', φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of C)).symm.surjective l
  rw [SpecToEquivOfLocalRing_symm_apply] at hs hl
  dsimp only at hs hl
  have hmk : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk I)).hom :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hx : x' = x := by
    rw [← Spec.map_comp_assoc] at hl
    have : IsLocalHom (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)).hom :=
      @RingHom.isLocalHom_comp _ _ _ _ _ _ _ φ.hom hmk hφ
    have h1 := map_closedPoint (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I))
    rw [hl] at h1
    exact h1.symm.trans (map_closedPoint ψ)
  subst hx
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc] at hs
  have : Mono (Y.fromSpecStalk (f x')) :=
    SurjectiveOnStalks.mono_of_injective (Y.fromSpecStalk (f x')).isEmbedding.injective
  have key := Spec.map_injective ((cancel_mono _).1 hs)
  exact ⟨φ.hom, hφ, congrArg CommRingCat.Hom.hom key⟩

theorem pow_ne_top {A : Type} [CommRing A] [IsLocalRing A] (n : ℕ) :
    maximalIdeal A ^ (n + 1) ≠ ⊤ := fun h =>
  (maximalIdeal.isMaximal A).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self n.succ_ne_zero))

theorem isLocalRing_quot {A : Type} [CommRing A] [IsLocalRing A] (n : ℕ) :
    IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
  haveI := Ideal.Quotient.nontrivial_iff.2 (pow_ne_top (A := A) n)
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

theorem map_maximalIdeal_quot {A : Type} [CommRing A] [IsLocalRing A] (J : Ideal A)
    [IsLocalRing (A ⧸ J)] :
    (maximalIdeal A).map (Ideal.Quotient.mk J) = maximalIdeal (A ⧸ J) :=
  IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective

theorem isArtinianRing_quot {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    IsArtinianRing (A ⧸ maximalIdeal A ^ (n + 1)) := by
  haveI := isLocalRing_quot (A := A) n
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨n + 1, ?_⟩
  rw [← map_maximalIdeal_quot, ← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

theorem exists_retraction : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → ∀ (x : X) [IsNoetherianRing (Y.presheaf.stalk (f x))], Function.Surjective (f.residueFieldMap x).hom → ∀ n : ℕ, ∃ ψ : X.presheaf.stalk x →+* Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (n + 1), ψ.comp (f.stalkMap x).hom = Ideal.Quotient.mk _ := by
  intro X Y f H x _ hs n
  suffices h : ∃ ψ : X.presheaf.stalk x →+*
      Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (n + 1),
      IsLocalHom ψ ∧ ψ.comp (f.stalkMap x).hom = Ideal.Quotient.mk _ from
    let ⟨ψ, _, h⟩ := h; ⟨ψ, h⟩
  induction n with
  | zero =>
    let e : ResidueField (Y.presheaf.stalk (f x)) ≃+* ResidueField (X.presheaf.stalk x) :=
      RingEquiv.ofBijective (f.residueFieldMap x).hom ⟨(f.residueFieldMap x).hom.injective, hs⟩
    let q : (Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (0 + 1)) ≃+*
        ResidueField (Y.presheaf.stalk (f x)) :=
      Ideal.quotEquivOfEq (by rw [zero_add, pow_one])
    let r := (q.trans e).symm
    haveI := isLocalRing_quot (A := Y.presheaf.stalk (f x)) 0
    refine ⟨r.toRingHom.comp (residue _), ?_, ?_⟩
    · have : IsLocalHom r.toRingHom := IsLocalHom.of_surjective _ r.surjective
      infer_instance
    · ext a
      change r (residue _ ((f.stalkMap x).hom a)) = _
      rw [RingEquiv.symm_apply_eq]
      rfl
  | succ n ih =>
    obtain ⟨ψ, hψ, h⟩ := ih
    set A := Y.presheaf.stalk (f x) with hA
    haveI := isLocalRing_quot (A := A) n
    haveI := isLocalRing_quot (A := A) (n + 1)
    haveI := isArtinianRing_quot (A := A) (n + 1)
    have hle : maximalIdeal A ^ (n + 1 + 1) ≤ maximalIdeal A ^ (n + 1) :=
      Ideal.pow_le_pow_right (Nat.le_succ _)
    let I : Ideal (A ⧸ maximalIdeal A ^ (n + 1 + 1)) :=
      (maximalIdeal A ^ (n + 1)).map (Ideal.Quotient.mk _)
    let r : (A ⧸ maximalIdeal A ^ (n + 1)) ≃+* ((A ⧸ maximalIdeal A ^ (n + 1 + 1)) ⧸ I) :=
      (DoubleQuot.quotQuotEquivQuotOfLE hle).symm
    haveI : IsLocalRing ((A ⧸ maximalIdeal A ^ (n + 1 + 1)) ⧸ I) := r.isLocalRing
    have h1 : I ≤ maximalIdeal _ := by
      rw [← map_maximalIdeal_quot]
      exact Ideal.map_mono (Ideal.pow_le_self n.succ_ne_zero)
    have h2 : maximalIdeal _ * I = ⊥ := by
      rw [← map_maximalIdeal_quot, ← Ideal.map_mul, ← pow_succ', Ideal.map_quotient_self]
    have : IsLocalHom r.toRingHom := IsLocalHom.of_surjective _ r.surjective
    have hl : IsLocalHom (r.toRingHom.comp ψ) := inferInstance
    let π : A →+* A ⧸ maximalIdeal A ^ (n + 1 + 1) := Ideal.Quotient.mk _
    refine @step X Y f x _ _ _ I _ (H _ I h1 h2) (CommRingCat.ofHom π)
      (CommRingCat.ofHom (r.toRingHom.comp ψ)) hl ?_
    change (r.toRingHom.comp ψ).comp _ = _
    rw [RingHom.comp_assoc, h]
    ext a
    rfl

end GlobalTheory.SmallLift
