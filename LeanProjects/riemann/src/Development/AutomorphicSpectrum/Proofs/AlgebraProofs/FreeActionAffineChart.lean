import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsQuotientSchemeOfFiniteFlatSubgroup
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoequifiberedDiagramMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpecHomCompCoaction

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory.AffineQuotient
open TensorProduct Algebra.TensorProduct

namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart

set_option backward.isDefEq.respectTransparency false

abbrev modObjObj {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
    [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal] (M X : C) [MonObj M] [ModObj M X] :
    letI := Functor.monObjObj (F := F) (X := M); ModObj (F.obj M) (F.obj X) :=
  letI := Functor.monObjObj (F := F) (X := M)
  { smul := Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X]
    one_smul := by
      change (Functor.LaxMonoidal.ε F ≫ F.map η[M]) ▷ F.obj X ≫ Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X] = (λ_ (F.obj X)).hom
      rw [comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp,
        ModObj.one_smul_self, Functor.LaxMonoidal.left_unitality]
    mul_smul := by
      change (Functor.LaxMonoidal.μ F M M ≫ F.map μ[M]) ▷ F.obj X ≫ Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X] =
        (α_ _ _ _).hom ≫ F.obj M ◁ (Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X]) ≫ Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X]
      rw [comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp,
        ModObj.mul_smul_self, whiskerLeft_comp, Category.assoc,
        Functor.LaxMonoidal.μ_natural_right_assoc, ← F.map_comp, F.map_comp, F.map_comp]
      simp [Functor.LaxMonoidal.associativity_assoc] }

lemma comp_inv'' {C : Type*} [Category C] [CartesianMonoidalCategory C] {A : C} [GrpObj A] {T T' : C}
    (r : T' ⟶ T) (x : T ⟶ A) : r ≫ x⁻¹ = (r ≫ x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one])

section Affine

variable {R : Type} [CommRing R]

theorem exists_hopf (H : Over (Spec (CommRingCat.of R))) [GrpObj H] (hH : IsFiniteLocallyFree H.hom) :
    ∃ (Λ : Type) (_ : CommRing Λ) (_ : HopfAlgebra R Λ) (_ : Module.Finite R Λ)
      (_ : Module.Projective R Λ) (e : specOver R Λ ≅ H), IsMonHom e.hom := by
  obtain ⟨h1, h2, h3⟩ := hH
  have : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨⟨Λ⟩, ⟨e⟩⟩ := (essImage_hopfSpec (R := .of R) (G := Grp.mk H)).2 this
  let e' : specOver R Λ ≅ H := (Grp.forget _).mapIso e
  have h₁ : IsFinite (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have h₂ : Flat (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have h₃ : LocallyOfFinitePresentation (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have : Module.Finite R Λ := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h₁)
  have : Module.Flat R Λ := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h₂)
  have : Algebra.FinitePresentation R Λ :=
    RingHom.finitePresentation_algebraMap.1 ((LocallyOfFinitePresentation.SpecMap_iff _).1 h₃)
  have : Module.FinitePresentation R Λ :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  exact ⟨Λ, inferInstance, inferInstance, inferInstance,
    Module.Flat.projective_of_finitePresentation, e', e.hom.hom.isMonHom_hom⟩

theorem exists_alg (Z : Over (Spec (CommRingCat.of R))) [IsAffine Z.left] :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Nonempty (specOver R B ≅ Z) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.left.isoSpec.inv ≫ Z.hom)
  refine ⟨Γ(Z.left, ⊤), inferInstance, φ.hom.toAlgebra, ⟨Over.isoMk Z.left.isoSpec.symm ?_⟩⟩
  exact hφ.symm

section Coaction

variable {Λ B : Type} [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]

lemma specHom_surjective {S T : Type} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (t : specOver R T ⟶ specOver R S) : ∃ φ : S →ₐ[R] T, specHom φ = t := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective t.left
  have h : CommRingCat.ofHom (algebraMap R S) ≫ φ = CommRingCat.ofHom (algebraMap R T) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    exact Over.w t
  refine ⟨⟨φ.hom, fun r ↦ congr($h r)⟩, ?_⟩
  ext1
  rw [specHom_left]
  exact hφ

variable {H Z : Over (Spec (CommRingCat.of R))} [GrpObj H] [ModObj H Z]

theorem exists_rightCoaction (i : specOver R Λ ⟶ H) (v : specOver R B ≅ Z) :
    ∃ ρ : B →ₐ[R] B ⊗[R] Λ, specHom ρ ≫ v.hom =
      (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ i)⁻¹ •
        (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom) := by
  obtain ⟨ρ, hρ⟩ := specHom_surjective (((specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ i)⁻¹ •
        (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom)) ≫ v.inv)
  exact ⟨ρ, by simp [hρ]⟩

variable (i : specOver R Λ ⟶ H) (v : specOver R B ⟶ Z) (ρ : B →ₐ[R] B ⊗[R] Λ)
  (hρ : specHom ρ ≫ v = (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ i)⁻¹ •
    (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v))

include hρ

lemma specHom_comp_rightCoaction {T : Type} [CommRing T] [Algebra R T] (φ : B ⊗[R] Λ →ₐ[R] T) :
    specHom (φ.comp ρ) ≫ v =
      (specHom (φ.comp includeRight) ≫ i)⁻¹ • (specHom (φ.comp includeLeft) ≫ v) := by
  rw [specHom_comp, specHom_comp, specHom_comp, Category.assoc, hρ, ModObj.comp_smul, Category.assoc,
    Category.assoc, comp_inv'']

lemma rightCoaction_counit [IsMonHom i] [Mono v] (b : B) :
    TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b := by
  let φ : B ⊗[R] Λ →ₐ[R] B := Algebra.TensorProduct.lift (AlgHom.id R B)
    ((Algebra.ofId R B).comp (Bialgebra.counitAlgHom R Λ)) fun _ _ ↦ .all _ _
  have h := specHom_comp_rightCoaction i v ρ hρ φ
  rw [lift_comp_includeRight', lift_comp_includeLeft, specHom_counit, Category.assoc,
    IsMonHom.one_hom, ← Hom.one_def, inv_one, _root_.one_smul] at h
  have h' : specHom (φ.comp ρ) = specHom (AlgHom.id R B) := by
    rw [← cancel_mono v]; exact h
  have h1 : φ (ρ b) = b := congr($(specHom_injective h') b)
  refine Eq.trans ?_ h1
  generalize ρ b = z
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [φ, Algebra.smul_def, _root_.mul_comm]

lemma rightCoaction_assoc [IsMonHom i] [Mono v] (b : B) :
    TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b) := by
  let l : B →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := includeLeft
  let r₁ : Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := includeRight.comp includeLeft
  let r₂ : Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := includeRight.comp includeRight
  let φ₀ : B ⊗[R] Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := Algebra.TensorProduct.lift l r₁ fun _ _ ↦ .all _ _
  let φ₁ : B ⊗[R] Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) :=
    Algebra.TensorProduct.lift (φ₀.comp ρ) r₂ fun _ _ ↦ .all _ _
  let φ₂ : B ⊗[R] Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) :=
    Algebra.TensorProduct.lift l ((Algebra.TensorProduct.lift r₁ r₂ fun _ _ ↦ .all _ _).comp
      (Bialgebra.comulAlgHom R Λ)) fun _ _ ↦ .all _ _
  have h₀ := specHom_comp_rightCoaction i v ρ hρ φ₀
  have h₁ := specHom_comp_rightCoaction i v ρ hρ φ₁
  have h₂ := specHom_comp_rightCoaction i v ρ hρ φ₂
  rw [lift_comp_includeRight', lift_comp_includeLeft] at h₀ h₁ h₂
  have hm : specHom ((Algebra.TensorProduct.lift r₁ r₂ fun _ _ ↦ .all _ _).comp
      (Bialgebra.comulAlgHom R Λ)) ≫ i = (specHom r₁ ≫ i) * (specHom r₂ ≫ i) := by
    rw [specHom_lift_comul, MonObj.mul_comp]
  rw [h₀, ← mul_smul, ← mul_inv_rev, ← hm, ← h₂, cancel_mono] at h₁
  have h : φ₂ (ρ b) = φ₁ (ρ b) := congr($(specHom_injective h₁.symm) b)
  have e₁ (z : B ⊗[R] Λ) :
      TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ z) = φ₁ z := by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, φ₁,
        Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply]
      generalize ρ x = w
      induction w with
      | zero => simp
      | add x y hx hy => simp only [map_add, add_tmul, add_mul, hx, hy]
      | tmul x y => simp [φ₀, l, r₁, r₂]
  have e₂ (z : B ⊗[R] Λ) : (Coalgebra.comul (R := R) (A := Λ)).lTensor B z = φ₂ z := by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [LinearMap.lTensor_tmul, φ₂, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
        Bialgebra.comulAlgHom_apply]
      generalize Coalgebra.comul (R := R) y = w
      induction w with
      | zero => simp
      | add x y hx hy => simp only [map_add, tmul_add, mul_add, hx, hy]
      | tmul x y => simp [l, r₁, r₂]
  rw [e₁, e₂, h]

lemma rightCoaction_free [Mono i] [Mono v] [Module.Finite R Λ] (hf : IsFreeAction H Z) :
    Function.Surjective (productMap (includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) := by
  let m := productMap (includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ
  have : Epi (CommRingCat.ofHom m.toRingHom) := by
    refine ⟨fun {T} φ ψ h ↦ ?_⟩
    have hm (z) : φ (m z) = ψ (m z) := congr($h z)
    let : Algebra R T := (φ.hom.comp (algebraMap R (B ⊗[R] Λ))).toAlgebra
    let φ' : B ⊗[R] Λ →ₐ[R] T := ⟨φ.hom, fun _ ↦ rfl⟩
    let ψ' : B ⊗[R] Λ →ₐ[R] T := ⟨ψ.hom, fun r ↦ by
      have := hm (algebraMap R _ r)
      rw [AlgHom.commutes] at this
      exact this.symm⟩
    have h₁ : φ'.comp includeLeft = ψ'.comp (includeLeft : B →ₐ[R] B ⊗[R] Λ) := by
      ext b
      have := hm (b ⊗ₜ 1)
      rw [productMap_left_apply] at this
      exact this
    have h₂ : φ'.comp ρ = ψ'.comp ρ := by
      ext b
      have := hm (1 ⊗ₜ b)
      rw [productMap_right_apply] at this
      exact this
    have h₃ := specHom_comp_rightCoaction i v ρ hρ φ'
    rw [h₂, specHom_comp_rightCoaction i v ρ hρ ψ', h₁] at h₃
    have h₄ : specHom (φ'.comp includeRight) ≫ i = specHom (ψ'.comp includeRight) ≫ i := by
      set x := specHom (ψ'.comp (includeLeft : B →ₐ[R] B ⊗[R] Λ)) ≫ v
      set g₁ := specHom (φ'.comp (includeRight : Λ →ₐ[R] B ⊗[R] Λ)) ≫ i
      set g₂ := specHom (ψ'.comp (includeRight : Λ →ₐ[R] B ⊗[R] Λ)) ≫ i
      have : (g₁ * g₂⁻¹) • x = x := by
        rw [mul_smul, h₃, smul_inv_smul]
      exact mul_inv_eq_one.1 (hf _ _ _ this)
    have h₅ := specHom_injective ((cancel_mono i).1 h₄)
    have : φ' = ψ' := Algebra.TensorProduct.ext h₁ h₅
    ext1
    exact congr(($this).toRingHom)
  refine RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom m.toRingHom) ?_
  refine RingHom.Finite.of_comp_finite
    (f := (includeLeftRingHom : B →+* B ⊗[R] B)) ?_
  have : (CommRingCat.ofHom m.toRingHom).hom.comp (includeLeftRingHom : B →+* B ⊗[R] B) =
      algebraMap B (B ⊗[R] Λ) := by
    ext b
    simp [m]
  rw [this, RingHom.finite_algebraMap]
  infer_instance

end Coaction

lemma isIso_lift_spec {Λ B : Type} [CommRing Λ] [Algebra R Λ] [CommRing B] [Algebra R B]
    {H Z : Over (Spec (CommRingCat.of R))} (e : specOver R Λ ≅ H) (v : specOver R B ≅ Z) :
    IsIso (lift (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ e.hom)
      (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom)) := by
  have P₂ : IsPullback (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ)).left
      (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ)).left (specOver R B).hom (specOver R Λ).hom :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R B Λ)
  have P₃ : IsPullback (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ e.hom).left
      (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom).left H.hom Z.hom :=
    P₂.flip.of_iso (Iso.refl _) ((Over.forget _).mapIso e) ((Over.forget _).mapIso v) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  have P₄ : IsPullback (fst H Z).left (snd H Z).left H.hom Z.hom :=
    IsPullback.of_hasPullback H.hom Z.hom
  have e₁ : (lift (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ e.hom)
      (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom)).left = (P₃.isoIsPullback _ _ P₄).hom := by
    apply P₄.hom_ext
    · rw [IsPullback.isoIsPullback_hom_fst, ← Over.comp_left, lift_fst]
    · rw [IsPullback.isoIsPullback_hom_snd, ← Over.comp_left, lift_snd]
  have : IsIso (Over.forget _ |>.map (lift (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ e.hom)
      (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom))) := by
    have hl : IsIso (lift (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ e.hom)
      (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom)).left := by
      rw [e₁]; infer_instance
    exact hl
  exact isIso_of_reflects_iso _ (Over.forget _)

def invIso (H : Over (Spec (CommRingCat.of R))) [GrpObj H] : H ≅ H where
  hom := ι[H]
  inv := ι[H]
  hom_inv_id := by
    have h : ι[H] = (𝟙 H)⁻¹ := by rw [Hom.inv_def]; simp
    rw [h, comp_inv'', Category.comp_id, inv_inv]
  inv_hom_id := by
    have h : ι[H] = (𝟙 H)⁻¹ := by rw [Hom.inv_def]; simp
    rw [h, comp_inv'', Category.comp_id, inv_inv]

theorem affine_chart (H Z : Over (Spec (CommRingCat.of R))) [GrpObj H] [ModObj H Z]
    (hH : IsFiniteLocallyFree H.hom) (hf : IsFreeAction H Z) [IsAffine Z.left] :
    ∃ (Y : Scheme.{0}) (q : Z.left ⟶ Y), IsAffine Y ∧ IsFinite q ∧ Flat q ∧
      LocallyOfFinitePresentation q ∧ Surjective q ∧
      IsPullback (γ[H, Z] : H ⊗ Z ⟶ Z).left (snd H Z).left q q := by
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopf H hH
  obtain ⟨B, _, _, ⟨v⟩⟩ := exists_alg Z
  obtain ⟨ρ, hρ⟩ := exists_rightCoaction e.hom v
  have hs := rightCoaction_free e.hom v.hom ρ hρ hf
  obtain ⟨h₁, -, h₃, h₄⟩ := GlobalTheory.HopfQuot.finite_faithfullyFlat_ker ρ
    (rightCoaction_assoc e.hom v.hom ρ hρ) (rightCoaction_counit e.hom v.hom ρ hρ) hs
  let C : Subring B := ρ.toRingHom.eqLocus (includeLeft : B →ₐ[R] B ⊗[R] Λ).toRingHom
  let c : CommRingCat.of C ⟶ CommRingCat.of B := CommRingCat.ofHom C.subtype
  have po : IsPushout c c (CommRingCat.ofHom ρ.toRingHom)
      (CommRingCat.ofHom (includeLeft : B →ₐ[R] B ⊗[R] Λ).toRingHom) :=
    isPushout_equalizer ρ _ hs h₄
  have pb := isPullback_SpecMap_of_isPushout _ _ _ _ po
  have hk := isIso_lift_spec (e ≪≫ invIso H) v
  set k := lift (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ (e ≪≫ invIso H).hom)
      (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom) with hkdef
  have hk₁ : k ≫ γ[H, Z] = specHom ρ ≫ v.hom := by
    rw [hρ, Hom.smul_def, hkdef, Hom.inv_def]
    simp [invIso]
  have hk₂ : k ≫ snd H Z = specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom := by
    rw [hkdef, lift_snd]
  let q : Z.left ⟶ Spec (CommRingCat.of C) := v.inv.left ≫ Spec.map c
  have pb' : IsPullback (γ[H, Z] : H ⊗ Z ⟶ Z).left (snd H Z).left q q := by
    refine pb.of_iso ((Over.forget _).mapIso (asIso k)) ((Over.forget _).mapIso v)
      ((Over.forget _).mapIso v) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact congr(($hk₁).left).symm
    · exact congr(($hk₂).left).symm
    · simp [q]
    · simp [q]
  have f₁ : IsFinite (Spec.map c) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 h₁)
  have f₂ : Flat (Spec.map c) ∧ Surjective (Spec.map c) :=
    (flat_and_surjective_SpecMap_iff _).2 (RingHom.faithfullyFlat_algebraMap_iff.2 h₃)
  have := f₂.1
  have := f₂.2
  have hq₂ : Flat q := by dsimp [q]; infer_instance
  have hq₃ : Surjective q := by dsimp [q]; infer_instance
  have hq₄ : QuasiCompact q := by dsimp [q]; infer_instance
  refine ⟨_, q, inferInstance, by dsimp [q]; infer_instance, hq₂, ?_, hq₃, pb'⟩
  have h3 := hH.2.2
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFinitePresentation)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) pb'.flip ⟨⟨hq₃, hq₂⟩, hq₄⟩ ?_
  exact MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) H.hom Z.hom h3

end Affine

section Open

variable {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X]

theorem exists_openAction (V : X.left.Opens)
    (hst : (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V) :
    ∃ _ : ModObj G (Over.mk (V.ι ≫ X.hom)),
      (γ[G, Over.mk (V.ι ≫ X.hom)] : G ⊗ Over.mk (V.ι ≫ X.hom) ⟶ Over.mk (V.ι ≫ X.hom)) ≫
        (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X) =
      G ◁ (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X) ≫ γ[G, X] := by
  let Z : Over S := Over.mk (V.ι ≫ X.hom)
  let m : Z ⟶ X := Over.homMk V.ι rfl
  have : Mono m.left := inferInstanceAs (Mono V.ι)
  have : Mono m := Over.mono_of_mono_left m
  let u : G ⊗ Z ⟶ X := G ◁ m ≫ γ[G, X]
  have hu : Set.range u.left ⊆ Set.range V.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h1 : (G ◁ m).left p ∈ (snd G X).left ⁻¹ᵁ V := by
      change (snd G X).left ((G ◁ m).left p) ∈ V
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, whiskerLeft_snd, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact ((snd G Z).left p).2
    rw [← hst] at h1
    simpa [u, Scheme.Hom.comp_apply] using h1
  let t : G ⊗ Z ⟶ Z := Over.homMk (IsOpenImmersion.lift V.ι u.left hu) (by
    change IsOpenImmersion.lift V.ι u.left hu ≫ V.ι ≫ X.hom = _
    rw [IsOpenImmersion.lift_fac_assoc]
    exact Over.w u)
  have ht : t ≫ m = u := by
    ext1
    exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨{ smul := t, one_smul := ?_, mul_smul := ?_ }, ht⟩
  · apply (cancel_mono m).1
    change (η[G] ▷ Z ≫ t) ≫ m = (λ_ Z).hom ≫ m
    rw [Category.assoc, ht]
    simp only [u]
    rw [← whisker_exchange_assoc, ModObj.one_smul_self, leftUnitor_naturality]
  · apply (cancel_mono m).1
    change (μ[G] ▷ Z ≫ t) ≫ m = ((α_ G G Z).hom ≫ G ◁ t ≫ t) ≫ m
    simp only [Category.assoc, ht]
    simp only [u]
    rw [← whisker_exchange_assoc, ModObj.mul_smul_self, ← whiskerLeft_comp_assoc, ht]
    simp only [u, whiskerLeft_comp, Category.assoc]
    rw [associator_naturality_right_assoc]

theorem hasAffineChart_of_open (V : X.left.Opens)
    (hst : (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V)
    [ModObj G (Over.mk (V.ι ≫ X.hom))]
    (hm : (γ[G, Over.mk (V.ι ≫ X.hom)] : G ⊗ Over.mk (V.ι ≫ X.hom) ⟶ Over.mk (V.ι ≫ X.hom)) ≫
        (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X) =
      G ◁ (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X) ≫ γ[G, X])
    (Y : Scheme.{0}) (q : V.toScheme ⟶ Y) (hY : IsAffine Y) (h₁ : IsFinite q) (h₂ : Flat q)
    (h₃ : LocallyOfFinitePresentation q) (h₄ : Surjective q)
    (pb : IsPullback (γ[G, Over.mk (V.ι ≫ X.hom)] : G ⊗ Over.mk (V.ι ≫ X.hom) ⟶ Over.mk (V.ι ≫ X.hom)).left
      (snd G (Over.mk (V.ι ≫ X.hom))).left q q) :
    HasAffineChart (γ[G, X] : G ⊗ X ⟶ X).left (snd G X).left V := by
  let Z : Over S := Over.mk (V.ι ≫ X.hom)
  let m : Z ⟶ X := Over.homMk V.ι rfl
  have P : IsPullback (G ◁ m) (snd G Z) (snd G X) m := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.fst ≫ fst G X) s.snd) ?_ ?_ ?_⟩⟩
    · intro s
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · simpa using s.condition.symm
    · intro s
      simp
    · intro s t h1 h2
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, ← h1]; simp
      · rw [lift_snd, h2]
  have P' : IsPullback (G ◁ m).left (snd G Z).left (snd G X).left V.ι := P.map (Over.forget S)
  have Q := (isPullback_morphismRestrict (snd G X).left V).flip
  let ε := P'.isoIsPullback _ _ Q
  have hε₁ : ε.inv ≫ (G ◁ m).left = ((snd G X).left ⁻¹ᵁ V).ι := P'.isoIsPullback_inv_fst _ _ Q
  have hε₂ : ε.inv ≫ (snd G Z).left = (snd G X).left ∣_ V := P'.isoIsPullback_inv_snd _ _ Q
  refine ⟨hst, Y, q, ε.inv ≫ (γ[G, Z] : G ⊗ Z ⟶ Z).left, hY, h₁, h₂, h₃, h₄, ?_, ?_⟩
  · have h := congr(($hm).left)
    rw [Over.comp_left, Over.comp_left] at h
    rw [Category.assoc]
    refine (congrArg (ε.inv ≫ ·) h).trans ?_
    rw [← Category.assoc, hε₁]
  · refine pb.of_iso ε (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp
    · rw [← hε₂, ε.hom_inv_id_assoc]; exact Category.comp_id _

end Open

section Base

theorem mono_of_free {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X]
    (hf : IsFreeAction G X) : Mono (lift (γ[G, X] : G ⊗ X ⟶ X) (snd G X)) := by
  refine ⟨fun {T} a b h ↦ ?_⟩
  have h₁ : a ≫ γ[G, X] = b ≫ γ[G, X] := by
    simpa using congr($h ≫ fst X X)
  have h₂ : a ≫ snd G X = b ≫ snd G X := by
    simpa using congr($h ≫ snd X X)
  have ea : ∀ c : T ⟶ G ⊗ X, c ≫ γ[G, X] = (c ≫ fst G X) • (c ≫ snd G X) := by
    intro c
    rw [Hom.smul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
  rw [ea a, ea b, ← h₂] at h₁
  have : ((b ≫ fst G X)⁻¹ * (a ≫ fst G X)) • (a ≫ snd G X) = a ≫ snd G X := by
    rw [mul_smul, h₁, inv_smul_smul]
  have h₃ := hf _ _ _ this
  apply CartesianMonoidalCategory.hom_ext
  · exact (inv_mul_eq_one.1 h₃).symm
  · exact h₂

theorem free_of_mono {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X]
    (h : Mono (lift (γ[G, X] : G ⊗ X ⟶ X) (snd G X))) : IsFreeAction G X := by
  intro T g x e
  have e₁ : lift g x ≫ lift (γ[G, X] : G ⊗ X ⟶ X) (snd G X) =
      lift (1 : T ⟶ G) x ≫ lift (γ[G, X] : G ⊗ X ⟶ X) (snd G X) := by
    rw [comp_lift, comp_lift, ← Hom.smul_def, ← Hom.smul_def, e, _root_.one_smul, lift_snd, lift_snd]
  have := (cancel_mono _).1 e₁
  simpa using congr($this ≫ fst G X)

variable {S S' : Scheme.{0}} (j : S' ⟶ S)

lemma isIso_pullback_fst [Mono j] (W : Over S) (z : W.left ⟶ S') (hz : z ≫ j = W.hom) :
    IsIso (pullback.fst W.hom j) := by
  refine ⟨pullback.lift (𝟙 _) z (by simp [hz]), ?_, by simp⟩
  apply pullback.hom_ext
  · simp
  · rw [← cancel_mono j]
    simp [pullback.condition, hz]

theorem baseChange_compare [Mono j] (G Z : Over S) [GrpObj G] [ModObj G Z] (z : Z.left ⟶ S')
    (hz : z ≫ j = Z.hom) :
    letI := Functor.grpObjObj (F := Over.pullback j) (G := G)
    letI := modObjObj (Over.pullback j) G Z
    IsIso (pullback.fst Z.hom j) ∧
      ∃ e : (((Over.pullback j).obj G) ⊗ ((Over.pullback j).obj Z)).left ≅ (G ⊗ Z).left,
      e.hom ≫ (γ[G, Z] : G ⊗ Z ⟶ Z).left =
        (γ[(Over.pullback j).obj G, (Over.pullback j).obj Z] :
          ((Over.pullback j).obj G) ⊗ ((Over.pullback j).obj Z) ⟶ (Over.pullback j).obj Z).left ≫
          pullback.fst Z.hom j ∧
      e.hom ≫ (snd G Z).left =
        (snd ((Over.pullback j).obj G) ((Over.pullback j).obj Z)).left ≫ pullback.fst Z.hom j := by
  refine ⟨isIso_pullback_fst j Z z hz, ?_⟩
  have iW : IsIso (pullback.fst (G ⊗ Z).hom j) :=
    isIso_pullback_fst j (G ⊗ Z) ((snd G Z).left ≫ z)
      (by rw [Category.assoc, hz]; exact Over.w (snd G Z))
  have nat : ∀ {A B : Over S} (f : A ⟶ B), ((Over.pullback j).map f).left ≫ pullback.fst B.hom j =
      pullback.fst A.hom j ≫ f.left := by
    intro A B f
    simp
  refine ⟨(Over.forget _).mapIso (Functor.Monoidal.μIso (Over.pullback j) G Z) ≪≫
    asIso (pullback.fst (G ⊗ Z).hom j), ?_, ?_⟩
  · change (Functor.LaxMonoidal.μ (Over.pullback j) G Z).left ≫ pullback.fst (G ⊗ Z).hom j ≫ _ = (Functor.LaxMonoidal.μ (Over.pullback j) G Z ≫ (Over.pullback j).map γ[G, Z]).left ≫ _
    rw [← nat, Over.comp_left, Category.assoc]
  · rw [← Functor.Monoidal.μ_snd (Over.pullback j) G Z]
    change (Functor.LaxMonoidal.μ (Over.pullback j) G Z).left ≫ pullback.fst (G ⊗ Z).hom j ≫ _ = (Functor.LaxMonoidal.μ (Over.pullback j) G Z ≫ (Over.pullback j).map (snd G Z)).left ≫ _
    rw [← nat, Over.comp_left, Category.assoc]

theorem baseChange_free (G Z : Over S) [GrpObj G] [ModObj G Z] (hf : IsFreeAction G Z) :
    letI := Functor.grpObjObj (F := Over.pullback j) (G := G)
    letI := modObjObj (Over.pullback j) G Z
    IsFreeAction ((Over.pullback j).obj G) ((Over.pullback j).obj Z) := by
  letI := Functor.grpObjObj (F := Over.pullback j) (G := G)
  letI := modObjObj (Over.pullback j) G Z
  apply free_of_mono
  have := mono_of_free G Z hf
  have hm : Mono ((Over.pullback j).map (lift (γ[G, Z] : G ⊗ Z ⟶ Z) (snd G Z))) := inferInstance
  have key : Functor.LaxMonoidal.μ (Over.pullback j) G Z ≫
        (Over.pullback j).map (lift (γ[G, Z] : G ⊗ Z ⟶ Z) (snd G Z)) =
      lift (γ[(Over.pullback j).obj G, (Over.pullback j).obj Z] :
          ((Over.pullback j).obj G) ⊗ ((Over.pullback j).obj Z) ⟶ (Over.pullback j).obj Z)
        (snd _ _) ≫ Functor.LaxMonoidal.μ (Over.pullback j) Z Z := by
    rw [← cancel_mono (Functor.OplaxMonoidal.δ (Over.pullback j) Z Z)]
    simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, Category.assoc, Category.assoc, Functor.OplaxMonoidal.δ_fst, ← Functor.map_comp,
        lift_fst]
      rfl
    · rw [lift_snd, Category.assoc, Category.assoc, Functor.OplaxMonoidal.δ_snd, ← Functor.map_comp,
        lift_snd, Functor.Monoidal.μ_snd]
  have : Mono (lift (γ[(Over.pullback j).obj G, (Over.pullback j).obj Z] :
          ((Over.pullback j).obj G) ⊗ ((Over.pullback j).obj Z) ⟶ (Over.pullback j).obj Z)
        (snd _ _) ≫ Functor.LaxMonoidal.μ (Over.pullback j) Z Z) := by
    rw [← key]; infer_instance
  exact mono_of_mono _ (Functor.LaxMonoidal.μ (Over.pullback j) Z Z)

end Base

theorem hasAffineChart_of_stable : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X],
    IsFiniteLocallyFree G.hom → IsFreeAction G X → ∀ (V : X.left.Opens) (W : S.Opens),
    IsAffineOpen V → IsAffineOpen W → V ≤ X.hom ⁻¹ᵁ W →
    (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V →
    HasAffineChart (γ[G, X] : G ⊗ X ⟶ X).left (snd G X).left V := by
  intro S G X _ _ hG hf V W hV hW hVW hst
  obtain ⟨_, hm⟩ := exists_openAction G X V hst
  let j : Spec (CommRingCat.of Γ(S, W)) ⟶ S := hW.fromSpec
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  let Z : Over S := Over.mk (V.ι ≫ X.hom)
  let m : Z ⟶ X := Over.homMk V.ι rfl
  have : Mono m.left := inferInstanceAs (Mono V.ι)
  have : Mono m := Over.mono_of_mono_left m
  have hZ : Set.range Z.hom ⊆ Set.range j := by
    rintro _ ⟨v, rfl⟩
    rw [show Set.range j = W from hW.range_fromSpec]
    exact hVW v.2
  let z := IsOpenImmersion.lift j Z.hom hZ
  have hz : z ≫ j = Z.hom := IsOpenImmersion.lift_fac j Z.hom hZ
  have hfZ : IsFreeAction G Z := by
    intro T g x e
    refine hf T g (x ≫ m) ?_
    have e₁ : g • (x ≫ m) = (g • x) ≫ m := by
      rw [Hom.smul_def, Hom.smul_def, Category.assoc, hm, ← Category.assoc, lift_whiskerLeft]
    rw [e₁, e]
  letI := Functor.grpObjObj (F := Over.pullback j) (G := G)
  letI := modObjObj (Over.pullback j) G Z
  obtain ⟨hi, e, he₁, he₂⟩ := baseChange_compare j G Z z hz
  have hfZ' := baseChange_free j G Z hfZ
  have hH : IsFiniteLocallyFree ((Over.pullback j).obj G).hom := by
    obtain ⟨a, b, c⟩ := hG
    exact ⟨inferInstanceAs (IsFinite (pullback.snd G.hom j)),
      inferInstanceAs (Flat (pullback.snd G.hom j)),
      inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.hom j))⟩
  have : IsAffine ((Over.pullback j).obj Z).left := by
    have : IsAffine Z.left := hV
    exact IsAffine.of_isIso (pullback.fst Z.hom j)
  obtain ⟨Y, q', a1, a2, a3, a4, a5, pb⟩ := affine_chart _ _ hH hfZ'
  refine hasAffineChart_of_open G X V hst hm Y (inv (pullback.fst Z.hom j) ≫ q') a1 (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance) ?_
  refine pb.of_iso e (asIso (pullback.fst Z.hom j)) (asIso (pullback.fst Z.hom j)) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact he₁.symm
  · exact he₂.symm
  · simp
  · simp

end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
