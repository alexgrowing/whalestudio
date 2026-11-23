import Mathlib

universe u v

open TensorProduct

namespace PI.UnitaryGroupMassFormula.MF

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] (x : A)

lemma quot_smul_mk (a : A) (b : B) :
    (Ideal.Quotient.mk (Ideal.span {x}) a) • (Ideal.Quotient.mk ((Ideal.span {x}).map (algebraMap A B)) b) =
      Ideal.Quotient.mk _ (algebraMap A B a * b) := by
  simp [Algebra.smul_def]

variable (J : Ideal (A ⧸ Ideal.span {x}))

lemma quot_smul_J (a : A) (j : J) : (Ideal.Quotient.mk (Ideal.span {x}) a) • j = a • j := by
  rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]

lemma x_smul_J (j : J) : x • j = 0 := by
  rw [← quot_smul_J]
  ext
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)]

noncomputable def toQuotTensor :
    B ⊗[A] J →+ (B ⧸ (Ideal.span {x}).map (algebraMap A B)) ⊗[A ⧸ Ideal.span {x}] J :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun j => Ideal.Quotient.mk _ b ⊗ₜ j) (fun j j' => tmul_add _ _ _))
      (fun b b' => by ext j; simp [add_tmul]))
    (fun a b j => by
      simp only [AddMonoidHom.mk'_apply]
      rw [Algebra.smul_def, ← quot_smul_mk, smul_tmul, quot_smul_J])

@[simp] lemma toQuotTensor_tmul (b : B) (j : J) :
    toQuotTensor x J (b ⊗ₜ j) = Ideal.Quotient.mk _ b ⊗ₜ j := rfl

noncomputable def tmulHom : B →ₗ[B] (J →+ B ⊗[A] J) where
  toFun b := (TensorProduct.mk A B J b).toAddMonoidHom
  map_add' b b' := by ext j; simp
  map_smul' c b := by ext j; simp [smul_tmul']

lemma tmulHom_vanish : (Ideal.span {x}).map (algebraMap A B) ≤ LinearMap.ker (tmulHom x J) := by
  rw [Ideal.map_span, Set.image_singleton]
  intro y hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [LinearMap.mem_ker]
  ext j
  simp only [tmulHom, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply,
    AddMonoidHom.zero_apply]
  rw [mul_comm, ← Algebra.smul_def, smul_tmul, x_smul_J, tmul_zero]

noncomputable def fromQuotTensor :
    (B ⧸ (Ideal.span {x}).map (algebraMap A B)) ⊗[A ⧸ Ideal.span {x}] J →+ B ⊗[A] J :=
  TensorProduct.liftAddHom ((Submodule.liftQ _ (tmulHom x J) (tmulHom_vanish x J)).toAddMonoidHom)
    (fun r m j => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [quot_smul_mk, quot_smul_J]
      simp only [LinearMap.toAddMonoidHom_coe]
      erw [Submodule.liftQ_apply, Submodule.liftQ_apply]
      simp only [tmulHom, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
      rw [← Algebra.smul_def, smul_tmul])

noncomputable def quotMul :
    (B ⧸ (Ideal.span {x}).map (algebraMap A B)) ⊗[A ⧸ Ideal.span {x}] J →ₗ[A ⧸ Ideal.span {x}]
      (B ⧸ (Ideal.span {x}).map (algebraMap A B)) :=
  (TensorProduct.rid _ _).toLinearMap ∘ₗ (LinearMap.lTensor _ J.subtype)

end PI.UnitaryGroupMassFormula.MF
