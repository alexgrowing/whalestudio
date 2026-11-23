import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraConjCocyclesCoboundariesPeriodSmul
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerShimura_conj_cocycles_coboundaries_period_smul : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ), (∀ z ∈ Z1 Γ w, cj z ∈ Z1 Γ w) ∧ (∀ z ∈ B1 Γ w, cj z ∈ B1 Γ w) ∧ ∀ (f : ℍ → ℂ) (c : ℂ), per Γ w (c • f) = c • per Γ w f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul | exact GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul | (intros; apply GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul <;> assumption)
