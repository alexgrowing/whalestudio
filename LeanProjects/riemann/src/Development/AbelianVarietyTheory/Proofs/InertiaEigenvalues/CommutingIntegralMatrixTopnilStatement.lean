import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixTopnil
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_integral_matrix_topnil : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → ∀ w : Matrix (Fin n) (Fin n) E, w * N = N * w → (∀ i j, ‖w i j‖ ≤ 1) → ∀ M : ℕ, (∀ i j, ‖(w ^ M) i j‖ < 1) → ∀ i j, ‖w i j‖ < 1 := by
  first | exact @GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute | exact GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute | (intros; apply GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute <;> assumption)
