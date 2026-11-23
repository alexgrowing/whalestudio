import Mathlib

namespace GlobalTheory.TensorLeibnizRule

open TensorProduct

theorem lTensor_leibniz {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) (x y : TensorProduct ℂ R S) :
    (LinearMap.lTensor R (↑d : S →ₗ[ℂ] S) : TensorProduct ℂ R S → TensorProduct ℂ R S) (x * y) =
      x * (LinearMap.lTensor R (↑d : S →ₗ[ℂ] S) : TensorProduct ℂ R S → TensorProduct ℂ R S) y +
      y * (LinearMap.lTensor R (↑d : S →ₗ[ℂ] S) : TensorProduct ℂ R S → TensorProduct ℂ R S) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' s' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul, TensorProduct.tmul_add]
      rw [mul_comm r' r]
    | add y₁ y₂ h₁ h₂ =>
      rw [mul_add, map_add, h₁, h₂, map_add, mul_add, add_mul]
      abel
  | add x₁ x₂ h₁ h₂ =>
    rw [add_mul, map_add, h₁, h₂, map_add, add_mul, mul_add]
    abel

end GlobalTheory.TensorLeibnizRule
