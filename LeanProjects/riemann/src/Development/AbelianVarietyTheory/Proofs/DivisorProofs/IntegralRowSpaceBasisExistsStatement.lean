import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRowSpaceBasisExists
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_row_space_basis_exists : ∀ (O k : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k] [IsFractionRing O k] (m n : ℕ) (P : Matrix (Fin m) (Fin n) k), (∀ c, Matrix.vecMul c P = 0 → c = 0) → ∃ M : Matrix (Fin m) (Fin m) k, M.det ≠ 0 ∧ ∀ c : Fin m → k, (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔ ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M := by
  first | exact @GlobalTheory.exists_basis_matrix_of_integral_preimage | exact GlobalTheory.exists_basis_matrix_of_integral_preimage | (intros; apply GlobalTheory.exists_basis_matrix_of_integral_preimage <;> assumption)
