import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormSlashHoloDecay
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_slash_mdifferentiable_and_exp_decay : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex → ∀ (f : CuspForm Γ k) (σ : SL(2, ℤ)), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[k] σ) ∧ ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖(⇑f ∣[k] σ) τ‖ ≤ C * Real.exp (-c * τ.im) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspForm_slash_holo_decay | exact GlobalTheory.HeckeFamilyMatrices.cuspForm_slash_holo_decay | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspForm_slash_holo_decay <;> assumption)
