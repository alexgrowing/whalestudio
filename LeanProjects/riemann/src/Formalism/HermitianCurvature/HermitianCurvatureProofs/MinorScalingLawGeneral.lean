import Formalism.HermitianCurvature.StatementX

namespace Formalism.FourierDecayAlt.P

open Matrix

namespace XGen

theorem scaled_eq {K : Type} [Field K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K) (α β : Fin n → K)
    (l : ℕ) (hl : l ≤ n) :
    (Matrix.of (fun a b : Fin n => α a * β b * Z a b)).submatrix
        (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun a : Fin l => α (Fin.castLE hl a)) *
          Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun a : Fin l => β (Fin.castLE hl a)) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

end XGen

theorem minor_scaling_law_general : Formalism.FourierDecayAlt.X.MinorScaleGen := by
  intro K _ n Z α β l hl
  rw [XGen.scaled_eq n Z α β l hl, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_diagonal, Finset.prod_mul_distrib]
  ring

end Formalism.FourierDecayAlt.P
