import Mathlib

namespace GlobalTheory

open scoped TensorProduct

theorem annihilator_diagonal_form_swap {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    {d : ℕ} (b : Fin d → B) (M : Matrix (Fin d) (Fin d) R)
    (h : ∀ x : B, (∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j)) *
      (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0)
    (f : B →ₗ[R] R) (y : B) :
    ∑ i, ∑ j, (M i j * f (b i * y)) • b j = ∑ i, ∑ j, (M i j * f (b i)) • (b j * y) := by
  classical
  let L : TensorProduct R B B →ₗ[R] B :=
    TensorProduct.lift ((LinearMap.lsmul R B).compl₁₂ f LinearMap.id)
  have hL : ∀ a c : B, L (TensorProduct.tmul R a c) = f a • c := fun a c => by simp [L]
  have e := h y
  rw [mul_sub, sub_eq_zero] at e
  simp only [Finset.sum_mul, smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one] at e
  have e2 := congrArg L e
  simp only [map_sum, map_smul, hL, smul_smul] at e2
  exact e2

theorem annihilator_diagonal_trace {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    {d : ℕ} (b : Module.Basis (Fin d) R B) (M : Matrix (Fin d) (Fin d) R)
    (h : ∀ x : B, (∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j)) *
      (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0) :
    ∑ i, ∑ j, (M i j * Algebra.trace R B (b i)) • b j = ∑ i, ∑ j, M i j • (b i * b j) := by
  classical
  have htr : ∀ z : B, Algebra.trace R B z = ∑ k, b.repr (z * b k) k := by
    intro z
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
    simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  have key : ∀ k, ∑ i, ∑ j, (M i j * b.repr (b i * b k) k) • b j =
      ∑ i, ∑ j, (M i j * b.repr (b i) k) • (b j * b k) :=
    fun k => annihilator_diagonal_form_swap (fun i => b i) M h (b.coord k) (b k)
  have hij : ∀ i j, ∑ k, (M i j * b.repr (b i) k) • (b j * b k) = M i j • (b i * b j) := by
    intro i j
    conv_rhs => rw [mul_comm, ← b.sum_repr (b i)]
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, smul_smul]
  calc ∑ i, ∑ j, (M i j * Algebra.trace R B (b i)) • b j
      = ∑ i, ∑ j, ∑ k, (M i j * b.repr (b i * b k) k) • b j := by
        simp only [htr, Finset.mul_sum, Finset.sum_smul]
    _ = ∑ k, ∑ i, ∑ j, (M i j * b.repr (b i * b k) k) • b j := by
        symm
        exact Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm)
    _ = ∑ k, ∑ i, ∑ j, (M i j * b.repr (b i) k) • (b j * b k) :=
        Finset.sum_congr rfl fun k _ => key k
    _ = ∑ i, ∑ j, ∑ k, (M i j * b.repr (b i) k) • (b j * b k) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ j, M i j • (b i * b j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hij i j

end GlobalTheory
