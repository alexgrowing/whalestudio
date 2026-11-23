import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem pointMatrix_mul_leftMulMatrix {O B Ix : Type} [CommRing O] [CommRing B] [Algebra O B]
    [Fintype Ix] [DecidableEq Ix] (β : Module.Basis Ix O B) (e : Ix → (B →ₐ[O] O)) (y : B) :
    (Matrix.of fun a a' => e a (β a')) * Algebra.leftMulMatrix β y
      = Matrix.diagonal (fun a => e a y) * (Matrix.of fun a a' => e a (β a')) := by
  ext a a'
  rw [Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [Matrix.of_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [← map_mul]
  conv_rhs => rw [← β.sum_repr (y * β a')]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem trace_eq_sum_points {O B Ix : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B]
    [Fintype Ix] [DecidableEq Ix] (β : Module.Basis Ix O B) (e : Ix → (B →ₐ[O] O))
    (h : (Matrix.of fun a a' => e a (β a')).det ≠ 0) (y : B) :
    Algebra.trace O B y = ∑ a, e a y := by
  have h1 := pointMatrix_mul_leftMulMatrix β e y
  set P : Matrix Ix Ix O := Matrix.of fun a a' => e a (β a') with hP
  have h2 : P.det • Algebra.leftMulMatrix β y
      = P.adjugate * (Matrix.diagonal (fun a => e a y) * P) := by
    rw [← h1, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have h3 := congrArg Matrix.trace h2
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_diagonal,
    smul_eq_mul, smul_eq_mul] at h3
  rw [Algebra.trace_eq_matrix_trace β]
  exact mul_left_cancel₀ h h3

theorem discr_norm_eq_of_points :
    ∀ (O B Ix : Type) [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Fintype Ix]
      [DecidableEq Ix] (β : Module.Basis Ix O B) (e : Ix → (B →ₐ[O] O)),
      (Matrix.of fun a a' => e a (β a')).det ≠ 0 →
        Algebra.discr O β = (Matrix.of fun a a' => e a (β a')).det ^ 2 ∧
          ∀ y : B, Algebra.norm O y = ∏ a, e a y := by
  intro O B Ix _ _ _ _ _ _ β e h
  refine ⟨?_, fun y => ?_⟩
  · have ht : Algebra.traceMatrix O β
        = (Matrix.of fun a a' => e a (β a')).transpose * (Matrix.of fun a a' => e a (β a')) := by
      ext i j
      rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, trace_eq_sum_points β e h,
        Matrix.mul_apply]
      simp
    rw [Algebra.discr_def, ht, Matrix.det_mul, Matrix.det_transpose, sq]
  · have h1 := congrArg Matrix.det (pointMatrix_mul_leftMulMatrix β e y)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h1
    rw [Algebra.norm_eq_matrix_det β]
    exact mul_right_cancel₀ h h1

end GlobalTheory.KeyKa
