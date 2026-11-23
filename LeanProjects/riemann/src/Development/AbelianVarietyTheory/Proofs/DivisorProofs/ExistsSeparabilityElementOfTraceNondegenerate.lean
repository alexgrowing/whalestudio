import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory.TraceCasimir

variable {A : Type} [Ring A] [Module.Free ℤ A] [Module.Finite ℤ A]

noncomputable def trL : A →ₗ[ℤ] ℤ := LinearMap.trace ℤ A ∘ₗ LinearMap.mul ℤ A

lemma trL_apply (z : A) : trL z = LinearMap.trace ℤ A (LinearMap.mulLeft ℤ z) := rfl

lemma trL_comm (x y : A) : trL (x * y) = trL (y * x) := by
  rw [trL_apply, trL_apply, LinearMap.mulLeft_mul, LinearMap.mulLeft_mul]
  exact LinearMap.trace_mul_comm ℤ _ _

lemma trL_eq_sum {n : ℕ} (b : Module.Basis (Fin n) ℤ A) (z : A) :
    trL z = ∑ k, b.repr (z * b k) k := by
  rw [trL_apply, LinearMap.trace_eq_matrix_trace ℤ b, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply]

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ A)

noncomputable def gram : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun k l => trL (b k * b l)

noncomputable def dualD (l : Fin n) : A := ∑ m, (gram b).adjugate m l • b m

lemma trL_mul_dualD (u : A) (l : Fin n) :
    trL (u * dualD b l) = ∑ m, (gram b).adjugate m l * trL (u * b m) := by
  simp only [dualD, Finset.mul_sum, mul_smul_comm, map_sum, map_zsmul, smul_eq_mul]

lemma trL_basis_mul_dualD (k l : Fin n) :
    trL (b k * dualD b l) = if k = l then (gram b).det else 0 := by
  rw [trL_mul_dualD]
  calc ∑ m, (gram b).adjugate m l * trL (b k * b m)
      = ∑ m, gram b k m * (gram b).adjugate m l :=
        Finset.sum_congr rfl fun m _ => mul_comm _ _
    _ = (gram b * (gram b).adjugate) k l := (Matrix.mul_apply).symm
    _ = _ := by rw [Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply]; split_ifs <;> simp

lemma det_mul_repr (u : A) (k : Fin n) :
    (gram b).det * b.repr u k = trL (u * dualD b k) := by
  conv_rhs => rw [← b.sum_repr u]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_zsmul, trL_basis_mul_dualD, smul_eq_mul]
  simp [mul_comm]

lemma det_smul_eq (u : A) : (gram b).det • u = ∑ l, trL (u * dualD b l) • b l := by
  conv_lhs => rw [← b.sum_repr u]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, det_mul_repr]

section Nondeg

variable (hnd : ∀ x : A, (∀ y : A, LinearMap.trace ℤ A (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0)
include hnd

lemma eq_zero_of_trL_mul_basis (v : A) (hv : ∀ k, trL (v * b k) = 0) : v = 0 := by
  apply hnd v
  intro y
  rw [← trL_apply]
  conv_lhs => rw [← b.sum_repr y]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_zsmul, hv, smul_zero,
    Finset.sum_const_zero]

lemma eq_zero_of_trL_basis_mul (v : A) (hv : ∀ k, trL (b k * v) = 0) : v = 0 :=
  eq_zero_of_trL_mul_basis b hnd v fun k => by rw [trL_comm]; exact hv k

lemma det_smul_eq' (u : A) : (gram b).det • u = ∑ l, trL (b l * u) • dualD b l := by
  rw [← sub_eq_zero]
  apply eq_zero_of_trL_basis_mul b hnd
  intro k
  simp only [mul_sub, Finset.mul_sum, mul_smul_comm, map_sub, map_sum, map_zsmul, smul_eq_mul,
    trL_basis_mul_dualD, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma det_ne_zero : (gram b).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  apply hv0
  have hx : ∑ k, v k • b k = 0 := by
    apply eq_zero_of_trL_mul_basis b hnd
    intro l
    have := congrFun hv l
    simp only [Matrix.vecMul, dotProduct, gram, Matrix.of_apply, Pi.zero_apply] at this
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_zsmul, smul_eq_mul]
    exact this
  funext k
  exact Fintype.linearIndependent_iff.mp b.linearIndependent v hx k

lemma sum_mul_dualD : ∑ k, b k * dualD b k = ((gram b).det : A) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_trL_mul_basis b hnd
  intro j
  rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
  have h1 : ∀ k, trL (b k * dualD b k * b j) = (gram b).det * b.repr (b j * b k) k := by
    intro k
    rw [trL_comm, ← mul_assoc, ← det_mul_repr]
  rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.mul_sum, ← trL_eq_sum b, ← zsmul_eq_mul,
    map_zsmul, smul_eq_mul, sub_self]

lemma balanced (c : A) :
    ∑ k, (c * b k) ⊗ₜ[ℤ] dualD b k = ∑ k, b k ⊗ₜ[ℤ] (dualD b k * c) := by
  haveI : Module.Free ℤ (A ⊗[ℤ] A) := Module.Free.of_basis (b.tensorProduct b)
  apply smul_right_injective (A ⊗[ℤ] A) (det_ne_zero b hnd)
  dsimp only
  simp only [Finset.smul_sum]
  have hL : ∀ k, (gram b).det • ((c * b k) ⊗ₜ[ℤ] dualD b k) =
      ∑ l, trL (c * b k * dualD b l) • (b l ⊗ₜ[ℤ] dualD b k) := by
    intro k
    rw [TensorProduct.smul_tmul', det_smul_eq, TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul']
  have hR : ∀ k, (gram b).det • (b k ⊗ₜ[ℤ] (dualD b k * c)) =
      ∑ l, trL (b l * (dualD b k * c)) • (b k ⊗ₜ[ℤ] dualD b l) := by
    intro k
    rw [← TensorProduct.tmul_smul, det_smul_eq' b hnd, TensorProduct.tmul_sum]
    simp only [TensorProduct.tmul_smul]
  simp only [hL, hR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [mul_assoc, trL_comm, mul_assoc]

end Nondeg

end GlobalTheory.TraceCasimir

open GlobalTheory.TraceCasimir in

theorem GlobalTheory.exists_separability_element_of_trace_nondegenerate :
    ∀ (A : Type) [Ring A] [Module.Free ℤ A] [Module.Finite ℤ A],
      (∀ x : A, (∀ y : A, LinearMap.trace ℤ A (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0) →
      ∃ (N : ℤ) (k : ℕ) (x y : Fin k → A), N ≠ 0 ∧ ∑ j, x j * y j = (N : A) ∧
        ∀ c : A, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c) := by
  intro A _ _ _ hnd
  let b := Module.finBasis ℤ A
  exact ⟨(gram b).det, _, b, dualD b, det_ne_zero b hnd, sum_mul_dualD b hnd, balanced b hnd⟩
