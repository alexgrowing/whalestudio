import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormsEqZeroOfPeriodSubConjCoboundary
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_eq_zero_of_period_sub_conj_coboundary : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)), per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) → f = 0 ∧ h = 0 := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem | exact GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem | (intros; apply GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem <;> assumption)
