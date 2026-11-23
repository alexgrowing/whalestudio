import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_minor_of_rank : ∀ (k : Type) [Field k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ρ : ℕ) (Y : Matrix A D k), ρ ≤ Y.rank → ∃ S : Fin ρ → A, ∃ τ : Fin ρ → D, (Y.submatrix S τ).det ≠ 0 := by
  first | exact @GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank | exact GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank | (intros; apply GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank <;> assumption)
