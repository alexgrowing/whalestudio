import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detSplit_of :
    DetSplit := by
  intro A _ m I _ _ P Q hPQ d
  have h1 : 1 - Q * P + Q * Matrix.diagonal d * P = 1 + Q * ((Matrix.diagonal d - 1) * P) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, ← Matrix.mul_assoc]
    abel
  rw [h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hPQ, Matrix.mul_one, add_sub_cancel,
    Matrix.det_diagonal]
