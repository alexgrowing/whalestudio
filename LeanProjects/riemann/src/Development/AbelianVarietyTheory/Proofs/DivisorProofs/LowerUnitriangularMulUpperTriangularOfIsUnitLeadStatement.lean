import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnitriangularMulUpperTriangularOfIsUnitLead
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lu_of_isUnit_leading_minors : ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R), (∀ (k : ℕ) (hk : k ≤ n), IsUnit (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) → ∃ L U : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, i < j → L i j = 0) ∧ (∀ i, L i i = 1) ∧ U.BlockTriangular id ∧ (∀ i, IsUnit (U i i)) ∧ M = L * U := by
  first | exact @GlobalTheory.lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors | exact GlobalTheory.lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors | (intros; apply GlobalTheory.lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors <;> assumption)
