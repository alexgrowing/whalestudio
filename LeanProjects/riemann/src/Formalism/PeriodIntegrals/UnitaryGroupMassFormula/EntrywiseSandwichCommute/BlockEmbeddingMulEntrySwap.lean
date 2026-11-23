import Mathlib
import Formalism.PeriodIntegrals.RTTIndependence
import Formalism.YangianSpanCharacter.YangianRTTProofs.RttRelation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstEmbeddingOne

namespace PI.QmSandwichWork

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P.W

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem tm_entry_comm (Y : ℂ) {p c ci x : A} (hp : Commute p x) (hc : Commute c x)
    (hci : Commute ci x) (i j : Fin 2) : Commute (Tm Y p c ci i j) x := by
  fin_cases i <;> fin_cases j
  · simpa [Tm] using (Algebra.commute_algebraMap_left Y x).add_left hp
  · simpa [Tm] using hc.neg_left
  · simpa [Tm] using hci
  · simp [Tm]

theorem swap_l {x y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A} (h : x * y = y * x)
    (Z : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) : x * (y * Z) = y * (x * Z) := by
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]

theorem flip_row (D : ℂ) (K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) :
    ((D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * K) (0, 0) (0, 0) =
      algebraMap ℂ A (D - 1) * K (0, 0) (0, 0) := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Pf, Matrix.one_apply,
    Algebra.algebraMap_eq_smul_one, sub_smul, sub_mul, smul_mul_assoc]

theorem flip_col (D : ℂ) (K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) :
    (K * (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)) (0, 0) (0, 0) =
      algebraMap ℂ A (D - 1) * K (0, 0) (0, 0) := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Pf, Matrix.one_apply,
    Algebra.algebraMap_eq_smul_one, sub_smul, sub_mul, mul_sub, mul_one, smul_mul_assoc, mul_smul_comm]

theorem block_embedding_mul_entry (M N : Matrix (Fin 2) (Fin 2) A) : (E1 M * E2 N) (0, 0) (0, 0) = M 0 0 * N 0 0 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, E1, E2]

theorem block_embedding_mul_entry_swap (M N : Matrix (Fin 2) (Fin 2) A) : (E2 N * E1 M) (0, 0) (0, 0) = N 0 0 * M 0 0 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, E1, E2]

end PI.QmSandwichWork
