import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionMatrixMul
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyDegreeSlashAction_matrix_mul : ∀ (w : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), p ∈ degreeLT ℂ (w + 1) → slP w (A * B) p = slP w B (slP w A p) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.SlashAction.polySlash_matrix_mul | exact GlobalTheory.HeckeFamilyMatrices.SlashAction.polySlash_matrix_mul | (intros; apply GlobalTheory.HeckeFamilyMatrices.SlashAction.polySlash_matrix_mul <;> assumption)
