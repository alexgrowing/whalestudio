import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariables
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables : ∀ (k : ℕ), 2 ≤ k → ∀ (f : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → ∀ σ : SL(2, ℤ), ∃ C : ℂ[X], ∀ τ : ℍ, slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] σ) τ + C := by
  first | exact @GlobalTheory.EichlerChange.polySlash_eichler_smul | exact GlobalTheory.EichlerChange.polySlash_eichler_smul | (intros; apply GlobalTheory.EichlerChange.polySlash_eichler_smul <;> assumption)
