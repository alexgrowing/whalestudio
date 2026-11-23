import Mathlib

namespace GlobalTheory.OneTensorExistence

open TensorProduct

theorem exists_one_tmul_eq (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ]
    [Algebra A Λ] (z : TensorProduct A (IsLocalRing.ResidueField A) Λ) :
    ∃ y : Λ, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] y = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul k l =>
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective k
    refine ⟨a • l, ?_⟩
    rw [← TensorProduct.smul_tmul, ← IsLocalRing.ResidueField.algebraMap_eq,
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨u + v, TensorProduct.tmul_add _ _ _⟩

end GlobalTheory.OneTensorExistence
