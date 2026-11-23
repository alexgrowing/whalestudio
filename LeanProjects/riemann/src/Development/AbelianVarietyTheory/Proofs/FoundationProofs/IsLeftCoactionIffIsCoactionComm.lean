import Mathlib

open TensorProduct Coalgebra

namespace GlobalTheory

variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']

structure IsCoaction (ρ : M →ₗ[R] M ⊗[R] C) : Prop where

  coassoc : ∀ m, TensorProduct.assoc R M C C (ρ.rTensor C (ρ m)) =
    (comul : C →ₗ[R] C ⊗[R] C).lTensor M (ρ m)

  counit : ∀ m, (counit : C →ₗ[R] R).lTensor M (ρ m) = m ⊗ₜ[R] (1 : R)

structure IsLeftCoaction (ρ : M →ₗ[R] C ⊗[R] M) : Prop where

  coassoc : ∀ m, TensorProduct.assoc R C C M ((comul : C →ₗ[R] C ⊗[R] C).rTensor M (ρ m)) =
    ρ.lTensor C (ρ m)

  counit : ∀ m, (counit : C →ₗ[R] R).rTensor M (ρ m) = (1 : R) ⊗ₜ[R] m

variable (R C) in

theorem isCoaction_comul : IsCoaction (comul : C →ₗ[R] C ⊗[R] C) where
  coassoc m := coassoc_apply m
  counit m := lTensor_counit_comul m

variable (R C) in

theorem isLeftCoaction_comul : IsLeftCoaction (comul : C →ₗ[R] C ⊗[R] C) where
  coassoc m := coassoc_apply m
  counit m := rTensor_counit_comul m

variable (M) in

theorem isCoaction_of_isGroupLikeElem {g : C} (hg : IsGroupLikeElem R g) :
    IsCoaction ((TensorProduct.mk R M C).flip g) where
  coassoc m := by simp [hg.comul_eq_tmul_self]
  counit m := by simp [hg.counit_eq_one]

theorem IsCoaction.rid_counit {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) (m : M) :
    TensorProduct.rid R M ((Coalgebra.counit : C →ₗ[R] R).lTensor M (ρ m)) = m := by
  simp [h.counit]

theorem IsCoaction.injective {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) : Function.Injective ρ :=
  Function.LeftInverse.injective
    (g := fun t => TensorProduct.rid R M ((Coalgebra.counit : C →ₗ[R] R).lTensor M t))
    h.rid_counit

theorem isLeftCoaction_iff_isCoaction_comm [IsCocomm R C] (ρ : M →ₗ[R] C ⊗[R] M) :
    IsLeftCoaction ρ ↔ IsCoaction ((TensorProduct.comm R C M).toLinearMap ∘ₗ ρ) := by

  let e : C ⊗[R] (C ⊗[R] M) ≃ₗ[R] M ⊗[R] (C ⊗[R] C) :=
    (TensorProduct.assoc R C C M).symm ≪≫ₗ TensorProduct.comm R _ _ ≪≫ₗ
      (TensorProduct.comm R C C).lTensor M
  have h1 : ∀ t : C ⊗[R] M, e (ρ.lTensor C t) = TensorProduct.assoc R M C C
      (((TensorProduct.comm R C M).toLinearMap ∘ₗ ρ).rTensor C (TensorProduct.comm R C M t)) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m =>
      simp only [LinearMap.lTensor_tmul, comm_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
        LinearEquiv.coe_coe]
      generalize ρ m = s
      induction s with
      | zero => simp
      | add a b ha hb => simp only [map_add, tmul_add, add_tmul, ha, hb]
      | tmul c' m' => simp [e]
  have h2 : ∀ t : C ⊗[R] M,
      e (TensorProduct.assoc R C C M ((comul : C →ₗ[R] C ⊗[R] C).rTensor M t)) =
      (comul : C →ₗ[R] C ⊗[R] C).lTensor M (TensorProduct.comm R C M t) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m => simp [e]
  have h3 : ∀ t : C ⊗[R] M, TensorProduct.comm R R M ((Coalgebra.counit : C →ₗ[R] R).rTensor M t) =
      (Coalgebra.counit : C →ₗ[R] R).lTensor M (TensorProduct.comm R C M t) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m => simp
  constructor
  · intro h
    refine ⟨fun m => ?_, fun m => ?_⟩
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← h1, ← h2, h.coassoc]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← h3, h.counit, comm_tmul]
  · intro h
    refine ⟨fun m => e.injective ?_, fun m => (TensorProduct.comm R R M).injective ?_⟩
    · rw [h1, h2]; exact (h.coassoc m).symm
    · rw [h3, comm_tmul]; exact h.counit m

def coactionWeightSpace (ρ : M →ₗ[R] M ⊗[R] C) (g : C) : Submodule R M :=
  LinearMap.eqLocus ρ ((TensorProduct.mk R M C).flip g)

omit [Coalgebra R C] in
@[simp] theorem mem_coactionWeightSpace {ρ : M →ₗ[R] M ⊗[R] C} {g : C} {m : M} :
    m ∈ coactionWeightSpace ρ g ↔ ρ m = m ⊗ₜ[R] g := Iff.rfl

omit [Coalgebra R C] in

theorem map_mem_coactionWeightSpace {ρ : M →ₗ[R] M ⊗[R] C} {ρ' : M' →ₗ[R] M' ⊗[R] C}
    {f : M →ₗ[R] M'} (hf : ∀ m, ρ' (f m) = f.rTensor C (ρ m)) {g : C} {m : M}
    (hm : m ∈ coactionWeightSpace ρ g) : f m ∈ coactionWeightSpace ρ' g := by
  rw [mem_coactionWeightSpace] at hm ⊢
  rw [hf, hm, LinearMap.rTensor_tmul]

end GlobalTheory
