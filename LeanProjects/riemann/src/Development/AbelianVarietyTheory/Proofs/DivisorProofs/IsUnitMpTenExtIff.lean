import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh
open scoped TensorProduct

namespace GlobalTheory.Obs.TenExt

variable {R : Type} [CommRing R] (N : Type) [AddCommGroup N] [Module R N]

theorem rTensor_smul {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (f : B →ₐ[R] B')
    (a : B) (m : B ⊗[R] N) :
    LinearMap.rTensor N f.toLinearMap (a • m) = f a • LinearMap.rTensor N f.toLinearMap m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def tenMap {T T' : C} (φ : T ⟶ T') :
    TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N) →ₐ[R] TrivSqZeroExt (F.obj T') (F.obj T' ⊗[R] N) where
  toFun c := TrivSqZeroExt.inl (mp F φ c.fst) + TrivSqZeroExt.inr (LinearMap.rTensor N (mp F φ).toLinearMap c.snd)
  map_one' := by ext <;> simp
  map_mul' c d := by
    ext
    · simp
    · simp [rTensor_smul]
  map_zero' := by ext <;> simp
  map_add' c d := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

@[simp] theorem fst_tenMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N)) :
    (tenMap N F φ c).fst = mp F φ c.fst := by simp [tenMap]

@[simp] theorem snd_tenMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N)) :
    (tenMap N F φ c).snd = LinearMap.rTensor N (mp F φ).toLinearMap c.snd := by simp [tenMap]

def tenExt : C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N))
  map φ := CommAlgCat.ofHom (tenMap N F φ)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext ((fst_tenMap N F _ c).trans (mp_id F T _)) (by
    refine (snd_tenMap N F _ c).trans ?_
    rw [show (mp F (𝟙 T)).toLinearMap = LinearMap.id from LinearMap.ext fun x ↦ mp_id F T x]
    simp))
  map_comp φ ψ := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext (by
    change (tenMap N F (φ ≫ ψ) c).fst = (tenMap N F ψ (tenMap N F φ c)).fst
    simp only [fst_tenMap]; exact mp_comp F φ ψ _) (by
    change (tenMap N F (φ ≫ ψ) c).snd = (tenMap N F ψ (tenMap N F φ c)).snd
    simp only [snd_tenMap]
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    congr 2
    exact LinearMap.ext fun x ↦ mp_comp F φ ψ x))

theorem mp_tenExt {T T' : C} (φ : T ⟶ T') (c : (tenExt N F).obj T) :
    mp (tenExt N F) φ c = tenMap N F φ c := rfl

theorem isUnit_mp_tenExt_iff {T S : C} (u : T ⟶ S) (c : (tenExt N F).obj T) :
    IsUnit (mp (tenExt N F) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_tenMap N F u c)))

theorem span_inl_eq_top {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (tenExt N F).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) (F.obj S ⊗[R] N))) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

end GlobalTheory.Obs.TenExt

namespace GlobalTheory.Obs.TenExt

variable {R : Type} [CommRing R] (N : Type) [AddCommGroup N] [Module R N]
variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem surj_key {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N))
    (y : TrivSqZeroExt (F.obj T') (F.obj T' ⊗[R] N)) (a₀ : F.obj T)
    (η₀ : F.obj T ⊗[R] N) (k₁ k₂ : ℕ) (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀)
    (hη : mp F l (c.fst ^ k₂) • y.snd = LinearMap.rTensor N (mp F l).toLinearMap η₀) :
    y * tenMap N F l c ^ (k₁ + k₂ + 1) = tenMap N F l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_tenMap, fst_tenMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul,
      map_pow] at ha ⊢
    linear_combination (mp F l c.fst) ^ (k₂ + 1) * ha
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, snd_tenMap, fst_tenMap, snd_tenMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul,
      rTensor_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢
    rw [← hη, ← ha]
    module

theorem ker_key {T : C} (c x : TrivSqZeroExt (F.obj T) (F.obj T ⊗[R] N)) (m₁ m₂ : ℕ)
    (h₁ : c.fst ^ m₁ * x.fst = 0) (h₂ : c.fst ^ m₂ • x.snd = 0) : c ^ (m₁ + m₂ + 1) * x = 0 := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero]
    linear_combination c.fst ^ (m₂ + 1) * h₁
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_zero, op_smul_eq_smul, Nat.pred_succ]
    linear_combination (norm := module) c.fst ^ (m₁ + 1) • h₂ + h₁ • ((m₁ + m₂ + 1) • c.fst ^ m₂ • c.snd)

theorem hasLoc_tenExt (H : Desc.HasLoc F) : Desc.HasLoc (tenExt N F) := by
  intro T c
  obtain ⟨T', l, h1, h2, h3, h4⟩ := H T c.fst
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  haveI : IsScalarTower R (F.obj T) (F.obj T') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((mp F l).commutes r).symm
  haveI := GlobalTheory.CechDR.FormExt.isLocalization_of_data F l c.fst h1 h2 h3
  have hp : ∀ m, LinearMap.rTensor N (mp F l).toLinearMap m =
      TensorProduct.AlgebraTensorModule.rTensor R N (Algebra.linearMap (F.obj T) (F.obj T')) m := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hs : ∀ (a : F.obj T) (η : F.obj T' ⊗[R] N), a • η = mp F l a • η := fun a η ↦
    (algebraMap_smul (F.obj T') a η).symm
  refine ⟨T', l, (isUnit_mp_tenExt_iff N F l c).2 h1, fun y ↦ ?_, fun x hx ↦ ?_,
    fun S u hu ↦ h4 S u ((isUnit_mp_tenExt_iff N F u c).1 hu)⟩
  · obtain ⟨⟨a₀, _, k₁, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers c.fst) y.fst
    obtain ⟨⟨η₀, _, k₂, rfl⟩, hη⟩ := IsLocalizedModule.surj (Submonoid.powers c.fst)
      (TensorProduct.AlgebraTensorModule.rTensor R N (Algebra.linearMap (F.obj T) (F.obj T'))) y.snd
    change y.fst * mp F l (c.fst ^ k₁) = mp F l a₀ at ha
    change (c.fst ^ k₂) • y.snd = _ at hη
    rw [hs, ← hp] at hη
    exact ⟨k₁ + k₂ + 1, _, surj_key N F l c y a₀ η₀ k₁ k₂ ha hη⟩
  · have e1 : mp F l x.fst = 0 :=
      (fst_tenMap N F l x).symm.trans (congrArg TrivSqZeroExt.fst hx)
    have e2 : TensorProduct.AlgebraTensorModule.rTensor R N (Algebra.linearMap (F.obj T) (F.obj T')) x.snd = 0 :=
      (hp _).symm.trans ((snd_tenMap N F l x).symm.trans (congrArg TrivSqZeroExt.snd hx))
    obtain ⟨m₁, h₁⟩ := h3 _ e1
    obtain ⟨⟨_, m₂, rfl⟩, h₂⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c.fst)
      (f := TensorProduct.AlgebraTensorModule.rTensor R N (Algebra.linearMap (F.obj T) (F.obj T'))) (x₁ := x.snd) (x₂ := 0)
      (by rw [e2, map_zero])
    rw [smul_zero, Submonoid.smul_def] at h₂
    exact ⟨m₁ + m₂ + 1, ker_key N F c x m₁ m₂ h₁ h₂⟩

end GlobalTheory.Obs.TenExt
