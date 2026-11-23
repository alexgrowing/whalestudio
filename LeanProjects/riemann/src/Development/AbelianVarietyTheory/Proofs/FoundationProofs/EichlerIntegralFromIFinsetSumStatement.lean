import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromIFinsetSum
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerIntegralFromI_finset_sum : ∀ (w : ℕ) {ι : Type} [Fintype ι] (g : ι → ℍ → ℂ), (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g i)) → ∀ τ : ℍ, eichler w (∑ i, g i) τ = ∑ i, eichler w (g i) τ := by
  first | exact @GlobalTheory.EichlerSum.eichler_finset_sum | exact GlobalTheory.EichlerSum.eichler_finset_sum | (intros; apply GlobalTheory.EichlerSum.eichler_finset_sum <;> assumption)
