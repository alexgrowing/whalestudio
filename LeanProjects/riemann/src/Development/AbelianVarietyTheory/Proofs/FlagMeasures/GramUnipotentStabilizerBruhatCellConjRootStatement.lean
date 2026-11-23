import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramUnipotentStabilizer_bruhatCell_conj_root : ∀ (K : Type) [Field K] (N : ℕ) (L U : Matrix (Fin N) (Fin N) K) (p : Point K N), IsLoUni L → IsUpUni U → (∀ a, a ∈ stabU (L * ptMat p * U) ↔ U * a * U⁻¹ ∈ stabU (ptMat p)) ∧ (∀ x, x ∈ lieU (L * ptMat p * U) ↔ U * x * U⁻¹ ∈ lieU (ptMat p)) ∧ (∀ a, a ∈ stabU (ptMat p) ↔ IsUpUni a ∧ ∀ i j, i < j → (i, j) ∉ roots (ptMat p) → a i j = 0) ∧ (∀ x, x ∈ lieU (ptMat p) ↔ ∀ i j, (i, j) ∉ roots (ptMat p) → x i j = 0) := by
  first | exact @GlobalTheory.LoopV.Cell.stab_cell | exact GlobalTheory.LoopV.Cell.stab_cell | (intros; apply GlobalTheory.LoopV.Cell.stab_cell <;> assumption)
