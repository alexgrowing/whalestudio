import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneScalarAvoidingMatrixEigenvalues
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normOne_scalar_avoiding_matrix_eigenvalues : ∀ (D : D7) (n : ℕ) (γ : Matrix (Fin n) (Fin n) D.host.E), ∃ z : D.host.E, z * D.host.conj z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  first | exact @GlobalTheory.NormOneScalar.exists_norm_one_det_ne_zero | exact GlobalTheory.NormOneScalar.exists_norm_one_det_ne_zero | (intros; apply GlobalTheory.NormOneScalar.exists_norm_one_det_ne_zero <;> assumption)
