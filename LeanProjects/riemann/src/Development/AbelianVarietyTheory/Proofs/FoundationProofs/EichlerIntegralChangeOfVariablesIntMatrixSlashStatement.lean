import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralChangeOfVariablesIntMatrixSlash
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerIntegral_changeOfVariables_intMatrix_slash : ∀ (k : ℕ), 2 ≤ k → ∀ (f : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → ∀ (β : Matrix (Fin 2) (Fin 2) ℤ), 0 < β.det → ∀ τ : ℍ, slP (k - 2) β (eichler (k - 2) f (toGL β • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] toGL β) τ + slP (k - 2) β (eichler (k - 2) f (toGL β • UpperHalfPlane.I)) := by
  first | exact @GlobalTheory.EichlerChangeGL.polySlash_eichler_toGL_smul | exact GlobalTheory.EichlerChangeGL.polySlash_eichler_toGL_smul | (intros; apply GlobalTheory.EichlerChangeGL.polySlash_eichler_toGL_smul <;> assumption)
