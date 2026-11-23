import Mathlib

noncomputable def UpperTheory.Reformulated.B.MatrixHomeomorphOfGeneralLinearPair.mulH_pk :
    {K : Type} →
      [inst : Field K] →
        [inst_1 : TopologicalSpace K] →
          [IsTopologicalRing K] →
            {n d : ℕ} → GL (Fin n) K → GL (Fin d) K → Matrix (Fin n) (Fin d) K ≃ₜ Matrix (Fin n) (Fin d) K :=
  fun {K} _ _ _ {n d} a c =>
    { toFun := fun y => (a : Matrix (Fin n) (Fin n) K) * y * (c : Matrix (Fin d) (Fin d) K)
      invFun := fun y =>
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * y *
          ((c⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      left_inv := fun y => by
        beta_reduce
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
          Units.inv_mul, Matrix.one_mul]
      right_inv := fun y => by
        beta_reduce
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
          Units.mul_inv, Matrix.one_mul]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
