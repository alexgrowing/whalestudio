import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspidalOfEichlerPeriodSubConjMemCoboundaries
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_of_eichlerPeriod_sub_conj_mem_coboundaries : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → 3 ≤ k → ∀ (f : ModularForm Γ (k : ℤ)) (h : CuspForm Γ (k : ℤ)), per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) → ∃ f' : CuspForm Γ (k : ℤ), ⇑f' = ⇑f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspidal_of_per_sub_cj_mem | exact GlobalTheory.HeckeFamilyMatrices.cuspidal_of_per_sub_cj_mem | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspidal_of_per_sub_cj_mem <;> assumption)
