import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem epi_of_surj {X Y Z : Scheme.{0}} (p : X ⟶ Y) [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    (hp : Function.Surjective p) (f g : Y ⟶ Z) (h : p ≫ f = p ≫ g) : f = g := by
  have hbase : f.base = g.base := by
    ext y
    obtain ⟨x0, rfl⟩ := hp y
    have h0 := congrArg (fun k => k.base x0) h
    simpa using h0
  refine Scheme.Hom.ext hbase (fun U => ?_)
  haveI : Mono (p.app (g ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _ (p.app_injective _)
  rw [← cancel_mono (p.app (g ⁻¹ᵁ U))]
  have h1 := Scheme.Hom.congr_app h U
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at h1
  rw [Category.assoc, p.naturality, ← Category.assoc, h1]
  have key : ∀ {V W : X.Opens} (e : V = W) (e2 : X.presheaf.obj (Opposite.op V) = X.presheaf.obj (Opposite.op W)),
      X.presheaf.map (eqToHom e).op ≫ eqToHom e2 = 𝟙 _ := by
    intro V W e e2
    subst e
    simp
  simp [eqToHom_map, eqToHom_op]
  erw [key, Category.comp_id]

theorem std_of_inj {A B : CommRingCat.{0}} (φ : A ⟶ B) (h : Function.Injective φ) :
    IsSchemeTheoreticallyDominant (Spec.map φ) := by
  constructor
  rw [Scheme.ker_of_isAffine]
  have e : (Spec.map φ).appTop = (Scheme.ΓSpecIso A).hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv := by
    rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have hinj : Function.Injective (Spec.map φ).appTop.hom := by
    rw [e]
    exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).1.comp h).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).1
  rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
  ext U s
  simp

theorem joint_epi {D A B : Type} [CommRing D] [CommRing A] [CommRing B] (φ : D →+* A) (ψ : D →+* B)
    (hi : Function.Injective (φ.prod ψ)) (hs : Function.Surjective (Spec.map (CommRingCat.ofHom φ)))
    {Z : Scheme.{0}} (f g : Spec (CommRingCat.of D) ⟶ Z)
    (h₁ : Spec.map (CommRingCat.ofHom φ) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ g)
    (h₂ : Spec.map (CommRingCat.ofHom ψ) ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ g) : f = g := by
  have e1 : Spec.map (CommRingCat.ofHom (RingHom.fst A B)) ≫ Spec.map (CommRingCat.ofHom (φ.prod ψ)) =
      Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp]
    congr 1
  have e2 : Spec.map (CommRingCat.ofHom (RingHom.snd A B)) ≫ Spec.map (CommRingCat.ofHom (φ.prod ψ)) =
      Spec.map (CommRingCat.ofHom ψ) := by
    rw [← Spec.map_comp]
    congr 1
  have hp : Function.Surjective (Spec.map (CommRingCat.ofHom (φ.prod ψ))) := by
    intro y
    obtain ⟨a, ha⟩ := hs y
    refine ⟨Spec.map (CommRingCat.ofHom (RingHom.fst A B)) a, ?_⟩
    rw [← ha, ← e1]
    rfl
  have hcov : Spec.map (CommRingCat.ofHom (φ.prod ψ)) ≫ f = Spec.map (CommRingCat.ofHom (φ.prod ψ)) ≫ g := by
    rw [← cancel_epi (coprodSpec A B)]
    apply coprod.hom_ext
    · simp only [← Category.assoc, coprodSpec_inl]
      rw [e1]
      exact h₁
    · simp only [← Category.assoc, coprodSpec_inr]
      rw [e2]
      exact h₂
  haveI := std_of_inj (CommRingCat.ofHom (φ.prod ψ)) hi
  exact epi_of_surj (Spec.map (CommRingCat.ofHom (φ.prod ψ))) hp f g hcov

variable {S : Scheme.{0}} {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S)

abbrev ob (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R M))) ≫ x)

variable {M N P : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
  [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]

def hom (f : M →ₗ[R] N) : ob x N ⟶ ob x M :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r : 2
    exact (TrivSqZeroExt.map f).commutes r)

theorem hom_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) : hom x g ≫ hom x f = hom x (g ∘ₗ f) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map g).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (g ∘ₗ f)).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  apply TrivSqZeroExt.ext <;> simp

theorem hom_id : hom x (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  have h : CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.id : M →ₗ[R] M)).toRingHom = 𝟙 _ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    apply TrivSqZeroExt.ext <;> simp
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.id : M →ₗ[R] M)).toRingHom) = 𝟙 _
  rw [h, Spec.map_id]

def zsec : Over.mk x ⟶ ob x M :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = x
    rw [← Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R M)) ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom = 𝟙 _ := by
      ext r : 2
      exact (TrivSqZeroExt.fstHom R R M).commutes r
    rw [this, Spec.map_id, Category.id_comp])

def proj : ob x M ⟶ Over.mk x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R M)))) rfl

theorem zsec_hom (f : M →ₗ[R] N) : zsec x ≫ hom x f = zsec x := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R N).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  simp

theorem hom_zero : hom x (0 : M →ₗ[R] N) = proj x ≫ zsec x := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (0 : M →ₗ[R] N)).toRingHom) =
    Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R N))) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem ext_pair {Z : Over S} (f g : ob x (R × R) ⟶ Z)
    (h₁ : hom x (LinearMap.fst R R R) ≫ f = hom x (LinearMap.fst R R R) ≫ g)
    (h₂ : hom x (LinearMap.snd R R R) ≫ f = hom x (LinearMap.snd R R R) ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  refine joint_epi (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom
    (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom ?_ ?_ f.left g.left
    (congrArg CommaMorphism.left h₁) (congrArg CommaMorphism.left h₂)
  · intro a b hab
    have h1 := congrArg Prod.fst hab
    have h2 := congrArg Prod.snd hab
    apply TrivSqZeroExt.ext
    · simpa using congrArg TrivSqZeroExt.fst h1
    · apply Prod.ext
      · simpa using congrArg TrivSqZeroExt.snd h1
      · simpa using congrArg TrivSqZeroExt.snd h2
  · refine (PrimeSpectrum.isHomeomorph_comap _ (fun y => ⟨1, one_pos, ?_⟩) ?_).surjective
    · refine ⟨TrivSqZeroExt.inl y.fst + TrivSqZeroExt.inr (y.snd, 0), ?_⟩
      rw [pow_one]
      apply TrivSqZeroExt.ext <;> simp
    · intro z hz
      rw [RingHom.mem_ker] at hz
      have hz1 : z.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hz
      rw [mem_nilradical]
      refine ⟨2, ?_⟩
      have hz2 : z = TrivSqZeroExt.inr z.snd := TrivSqZeroExt.ext (by simp [hz1]) (by simp)
      rw [hz2, pow_two, TrivSqZeroExt.inr_mul_inr]

variable (G : Over S) [GrpObj G]

theorem isTanAt_iff (v : epsAt x ⟶ G) : IsTanAt G x v ↔ (zsec x : _ ⟶ ob x R) ≫ v = 1 := by
  constructor
  · intro h
    exact Over.OverMorphism.ext h
  · intro h
    exact congrArg CommaMorphism.left h

theorem hom_add (v : ob x R ⟶ G) (hv : zsec x ≫ v = 1) (f g : R →ₗ[R] M) :
    hom x (f + g) ≫ v = (hom x f ≫ v) * (hom x g ≫ v) := by
  have key : hom x (LinearMap.prod LinearMap.id LinearMap.id : R →ₗ[R] R × R) ≫ v =
      (hom x (LinearMap.inl R R R) ≫ v) * (hom x (LinearMap.inr R R R) ≫ v) := by
    apply ext_pair x
    · rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, ← Category.assoc, hom_comp, hom_comp, hom_comp]
      have e1 : (LinearMap.fst R R R) ∘ₗ (LinearMap.prod LinearMap.id LinearMap.id) =
          (LinearMap.id : R →ₗ[R] R) := LinearMap.ext fun _ => rfl
      have e2 : (LinearMap.fst R R R) ∘ₗ (LinearMap.inl R R R) = (LinearMap.id : R →ₗ[R] R) :=
        LinearMap.ext fun _ => rfl
      have e3 : (LinearMap.fst R R R) ∘ₗ (LinearMap.inr R R R) = (0 : R →ₗ[R] R) :=
        LinearMap.ext fun _ => rfl
      rw [e1, e2, e3, hom_id, hom_zero, Category.id_comp, Category.assoc, hv, MonObj.comp_one, _root_.mul_one]
    · rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, ← Category.assoc, hom_comp, hom_comp, hom_comp]
      have e1 : (LinearMap.snd R R R) ∘ₗ (LinearMap.prod LinearMap.id LinearMap.id) =
          (LinearMap.id : R →ₗ[R] R) := LinearMap.ext fun _ => rfl
      have e2 : (LinearMap.snd R R R) ∘ₗ (LinearMap.inl R R R) = (0 : R →ₗ[R] R) :=
        LinearMap.ext fun _ => rfl
      have e3 : (LinearMap.snd R R R) ∘ₗ (LinearMap.inr R R R) = (LinearMap.id : R →ₗ[R] R) :=
        LinearMap.ext fun _ => rfl
      rw [e1, e2, e3, hom_id, hom_zero, Category.id_comp, Category.assoc, hv, MonObj.comp_one, _root_.one_mul]
  have hf : f = (LinearMap.coprod f g) ∘ₗ (LinearMap.inl R R R) := LinearMap.ext fun r => by simp
  have hg : g = (LinearMap.coprod f g) ∘ₗ (LinearMap.inr R R R) := LinearMap.ext fun r => by simp
  have hfg : f + g = (LinearMap.coprod f g) ∘ₗ (LinearMap.prod LinearMap.id LinearMap.id) :=
    LinearMap.ext fun r => by simp
  rw [hfg, ← hom_comp, Category.assoc, key, MonObj.comp_mul, ← Category.assoc, ← Category.assoc,
    hom_comp, hom_comp, ← hf, ← hg]

variable [IsCommMonObj G]

def tanSub : Subgroup (ob x R ⟶ G) where
  carrier := {v | zsec x ≫ v = 1}
  mul_mem' {a b} ha hb := by
    change zsec x ≫ (a * b) = 1
    rw [MonObj.comp_mul, show zsec x ≫ a = 1 from ha, show zsec x ≫ b = 1 from hb, _root_.mul_one]
  one_mem' := MonObj.comp_one _
  inv_mem' {a} ha := by
    change zsec x ≫ a⁻¹ = 1
    rw [GrpObj.comp_inv, show zsec x ≫ a = 1 from ha, inv_one]

abbrev tanModule : Module R (Additive (tanSub x G)) where
  smul c v := Additive.ofMul ⟨hom x (c • LinearMap.id) ≫ v.toMul.1, by
    change zsec x ≫ _ = 1
    rw [← Category.assoc, zsec_hom]; exact v.toMul.2⟩
  one_smul v := Subtype.ext (by
    change hom x ((1 : R) • LinearMap.id) ≫ v.toMul.1 = v.toMul.1
    rw [one_smul, hom_id, Category.id_comp])
  mul_smul a b v := Subtype.ext (by
    change hom x ((a * b) • LinearMap.id) ≫ v.toMul.1 =
      hom x (a • LinearMap.id) ≫ hom x (b • LinearMap.id) ≫ v.toMul.1
    rw [← Category.assoc, hom_comp, LinearMap.smul_comp, LinearMap.id_comp, mul_smul])
  smul_zero a := Subtype.ext (MonObj.comp_one _)
  smul_add a v w := Subtype.ext (MonObj.comp_mul _ _ _)
  add_smul a b v := Subtype.ext (by
    change hom x ((a + b) • LinearMap.id) ≫ v.toMul.1 =
      (hom x (a • LinearMap.id) ≫ v.toMul.1) * (hom x (b • LinearMap.id) ≫ v.toMul.1)
    rw [add_smul, hom_add x G _ v.toMul.2])
  zero_smul v := Subtype.ext (by
    change hom x ((0 : R) • LinearMap.id) ≫ v.toMul.1 = 1
    rw [zero_smul, hom_zero, Category.assoc, show zsec x ≫ v.toMul.1 = 1 from v.toMul.2, MonObj.comp_one])

end GlobalTheory.CompanionTheory.Ar.LieEx

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieModel_exists (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (R : Type) [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module R E), Nonempty (LieModel G x E) := by
  letI := LieEx.tanModule x G
  refine ⟨Additive (LieEx.tanSub x G), inferInstance, LieEx.tanModule x G, ⟨?_⟩⟩
  exact
    { pt := fun e => e.toMul.1
      tan := fun e => (LieEx.isTanAt_iff x G _).2 e.toMul.2
      inj := fun e e' h => by
        apply Additive.toMul.injective
        exact Subtype.ext h
      onto := fun v hv => ⟨Additive.ofMul ⟨v, (LieEx.isTanAt_iff x G v).1 hv⟩, rfl⟩
      add := fun _ _ => rfl
      smul := fun _ _ => rfl }

end GlobalTheory.CompanionTheory.Ar
