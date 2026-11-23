import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoequifiberedDiagramMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpecHomCompCoaction

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineQuotient

set_option backward.isDefEq.respectTransparency false

open TensorProduct Algebra.TensorProduct in

lemma exists_coaction {R Λ : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ]
    {A : Over (Spec (CommRingCat.of R))} [GrpObj A] (i : specOver R Λ ⟶ A) {Y : Scheme.{0}}
    (f : A.left ⟶ Y) (g : (specOver R Λ ⊗ A).left ⟶ Y)
    (ha : ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A).left ≫ f = g)
    (hp : (snd (specOver R Λ) A).left ≫ f = g) (U : Y.Opens) (hf : IsAffineOpen (f ⁻¹ᵁ U))
    (hg : IsAffineOpen (g ⁻¹ᵁ U)) :
    ∃ (_ : Algebra R Γ(A.left, f ⁻¹ᵁ U)) (v : specOver R Γ(A.left, f ⁻¹ᵁ U) ⟶ A) (_ : Mono v)
      (ρ : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R] Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)
      (e : Γ((specOver R Λ ⊗ A).left, g ⁻¹ᵁ U) ⟶ .of (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)) (_ : IsIso e),
      specHom ρ ≫ v = (specHom includeRight ≫ i) * (specHom includeLeft ≫ v) ∧
      pullOver f g _ ha U ≫ e = CommRingCat.ofHom ρ.toRingHom ∧
      pullOver f g _ hp U ≫ e = CommRingCat.ofHom (includeLeft : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R]
        Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ).toRingHom := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hf.fromSpec ≫ A.hom)
  let : Algebra R Γ(A.left, f ⁻¹ᵁ U) := φ.hom.toAlgebra
  let v : specOver R Γ(A.left, f ⁻¹ᵁ U) ⟶ A := Over.homMk hf.fromSpec hφ.symm
  have : Mono v.left := inferInstanceAs (Mono hf.fromSpec)
  have P₁ : IsPullback (Spec.map (pullOver f g _ hp U))
      (hg.fromSpec ≫ (fst (specOver R Λ) A).left) (Spec.map φ) (specOver R Λ).hom := by
    rw [hφ]
    exact (isPullback_pullOver f g _ hp hf hg).paste_vert
      (IsPullback.of_hasPullback (specOver R Λ).hom A.hom).flip
  have P₂ : IsPullback (specHom (includeLeft : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R]
        Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)).left (specHom (includeRight : Λ →ₐ[R]
        Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)).left (Spec.map φ) (specOver R Λ).hom :=
    isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R Γ(A.left, f ⁻¹ᵁ U) Λ)
  obtain ⟨e, he⟩ := Spec.map_surjective (P₂.isoIsPullback _ _ P₁).hom
  have : IsIso (Spec.map e) := by rw [he]; infer_instance
  have : IsIso e := by
    have : IsIso (Scheme.Spec.map e.op) := this
    have := Spec.fullyFaithful.isIso_of_isIso_map e.op
    exact isIso_of_op e
  have h₁ := P₂.isoIsPullback_hom_fst _ _ P₁
  have h₂ := P₂.isoIsPullback_hom_snd _ _ P₁
  rw [← he] at h₁ h₂
  have hw : (Spec.map e ≫ hg.fromSpec) ≫ (specOver R Λ ⊗ A).hom =
      (specOver R (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)).hom := by
    rw [← Over.w (fst (specOver R Λ) A), Category.assoc, reassoc_of% h₂, Over.w]
  let k : specOver R (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ) ⟶ specOver R Λ ⊗ A :=
    Over.homMk (Spec.map e ≫ hg.fromSpec) hw
  have k₁ : k ≫ fst _ _ = specHom includeRight := by
    ext1
    rw [← h₂]
    exact Category.assoc ..
  have k₂ : k ≫ snd _ _ = specHom includeLeft ≫ v := by
    ext1
    rw [Over.comp_left, Over.comp_left, ← h₁]
    change (Spec.map e ≫ hg.fromSpec) ≫ _ = (Spec.map e ≫ _) ≫ hf.fromSpec
    rw [Category.assoc, Category.assoc, SpecMap_pullOver f g _ hp hf hg]
  have k₃ : (k ≫ ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A)).left =
      Spec.map (pullOver f g _ ha U ≫ e) ≫ hf.fromSpec := by
    rw [Spec.map_comp, Category.assoc, SpecMap_pullOver f g _ ha hf hg]
    exact Category.assoc ..
  have h₃ : φ ≫ pullOver f g _ ha U ≫ e =
      CommRingCat.ofHom (algebraMap R (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, ← Category.assoc, ← k₃, Over.w]
    rfl
  let ρ : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R] Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ :=
    ⟨(pullOver f g _ ha U ≫ e).hom, fun r ↦ congr($h₃ r)⟩
  refine ⟨inferInstance, v, Over.mono_of_mono_left v, ρ, e, this, ?_, rfl, ?_⟩
  · rw [← k₂, ← k₁, Category.assoc, ← comp_mul]
    ext1
    exact k₃.symm
  · apply Spec.map_injective
    rw [Spec.map_comp, h₁]
    rfl

lemma exists_quotient_hopf
    (hq : (∀ (R Λ B : Type) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] TensorProduct R B Λ), (∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b)) → (∀ b, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) → Module.Finite (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ Module.FaithfullyFlat (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ RingHom.ker (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ), z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}))
    {R Λ : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ]
    [Module.Projective R Λ]
    {A : Over (Spec (CommRingCat.of R))} [GrpObj A] [IsCommMonObj A] (i : specOver R Λ ⟶ A)
    [IsMonHom i] [Mono i] {Y : Over (Spec (CommRingCat.of R))} [IsLocallyNoetherian Y.left]
    (f : A ⟶ Y) [IsFinite f.left]
    (h : ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A) ≫ f = snd (specOver R Λ) A ≫ f) :
    ∃ (Q : Over (Spec (CommRingCat.of R))) (q : A ⟶ Q) (π : Q ⟶ Y), IsFinite π.left ∧
      IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A) (snd (specOver R Λ) A) q q := by
  have : IsAffine (specOver R Λ).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffineHom (specOver R Λ).hom := inferInstance
  have : IsAffineHom (snd (specOver R Λ) A).left :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) (specOver R Λ).hom A.hom this
  have ha : ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A).left ≫ f.left =
    (snd (specOver R Λ) A).left ≫ f.left := congr(($h).left)
  obtain ⟨Q, q, π, h₀, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient f.left _ _ ha _ rfl (fun U ↦ by
    obtain ⟨_, v, _, ρ, e, _, hρ, e₁, e₂⟩ :=
      exists_coaction i f.left _ ha rfl U.1 (U.2.preimage _) (U.2.preimage _)
    have hs := coaction_free i v ρ hρ
    obtain ⟨-, hff, hk⟩ := hq R Λ _ ρ (coaction_assoc i v ρ hρ) (coaction_counit i v ρ hρ) hs
    have hC : invariants f.left _ _ ha _ rfl U.1 = ρ.toRingHom.eqLocus
        (Algebra.TensorProduct.includeLeft : Γ(A.left, f.left ⁻¹ᵁ U.1) →ₐ[R] _).toRingHom := by
      ext x
      rw [mem_invariants, ← (ConcreteCategory.bijective_of_isIso e).1.eq_iff,
        ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e₁, e₂]
      rfl
    rw [hC]
    refine ⟨hff, ?_⟩
    refine (isPushout_equalizer ρ _ hs hk).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso e).symm (by simp) (by simp) ?_ ?_
    · rw [← e₁]; simp
    · rw [← e₂]; simp)
  refine ⟨Over.mk (π ≫ Y.hom), Over.homMk q (by simp [reassoc_of% h₀]), Over.homMk π rfl,
    h₁, h₂, h₃, h₄, ?_⟩
  exact IsPullback.of_map_of_faithful (Over.forget _) h₅

lemma exists_hopfAlgebra (R : Type) [CommRing R] [IsNoetherianRing R]
    (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsFinite H.hom] [Flat H.hom] :
    ∃ (Λ : Type) (_ : CommRing Λ) (_ : HopfAlgebra R Λ) (_ : Module.Finite R Λ)
      (_ : Module.Projective R Λ) (e : specOver R Λ ≅ H), IsMonHom e.hom := by
  have : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨⟨Λ⟩, ⟨e⟩⟩ := (essImage_hopfSpec (R := .of R) (G := Grp.mk H)).2 this
  let e' : specOver R Λ ≅ H := (Grp.forget _).mapIso e
  have h₁ : IsFinite (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have h₂ : Flat (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have : Module.Finite R Λ := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h₁)
  have : Module.Flat R Λ := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h₂)
  have : Module.FinitePresentation R Λ := Module.finitePresentation_of_finite R Λ
  exact ⟨Λ, inferInstance, inferInstance, inferInstance,
    Module.Flat.projective_of_finitePresentation, e', e.hom.hom.isMonHom_hom⟩

end GlobalTheory.AffineQuotient

namespace GlobalTheory

open AffineQuotient

set_option backward.isDefEq.respectTransparency false in

theorem exists_quotient_scheme_of_finite_flat_subgroup :
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsCommMonObj H], IsFinite H.hom → Flat H.hom → ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1) → (∀ (R Λ B : Type) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] TensorProduct R B Λ), (∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b)) → (∀ b, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) → Module.Finite (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ Module.FaithfullyFlat (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ RingHom.ker (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ), z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R))) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] (i : H ⟶ P.A), IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∃ (Q : Over (Spec (CommRingCat.of R))) (q : P.A ⟶ Q), IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧ IsPullback ((fst H P.A ≫ i) * snd H P.A) (snd H P.A) q q := by
  intro hk hq hm R _ _ P H _ i _ _ _ _
  have := P.isAb.comm
  have := P.isAb.proper
  have : IsCommMonObj H := ⟨by
    rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  obtain ⟨N, hN, hH⟩ := hk R H ‹_› ‹_›
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  have := (hm _ P N hN).1
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopfAlgebra R H
  have hi : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]
  obtain ⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient_hopf hq (e.hom ≫ i) (mulA P.A N) (by
    rw [mulA, comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow,
      ← comp_pow i, hi, comp_one, comp_one, _root_.one_mul])
  refine ⟨Q, q, h₂, h₃, h₄, ?_, ?_, ?_⟩
  · rw [← Over.w π]; infer_instance
  · rw [← Over.w π]; infer_instance
  · refine h₅.of_iso (whiskerRightIso e P.A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp [comp_mul]

end GlobalTheory
