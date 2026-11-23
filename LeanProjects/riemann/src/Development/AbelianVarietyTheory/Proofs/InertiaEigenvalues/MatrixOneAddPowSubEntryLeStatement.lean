import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixOneAddPowSubEntryLe
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (Y : Matrix n n E) (t : ℝ), 0 ≤ t → t ≤ 1 → (∀ i j, ‖Y i j‖ ≤ t) → ∀ (m : ℕ) i j, ‖((1 + Y) ^ m - 1 - (m : E) • Y) i j‖ ≤ t ^ 2 := by
  first | exact @GlobalTheory.matrix_one_add_pow_sub_entry_le | exact GlobalTheory.matrix_one_add_pow_sub_entry_le | (intros; apply GlobalTheory.matrix_one_add_pow_sub_entry_le <;> assumption)
