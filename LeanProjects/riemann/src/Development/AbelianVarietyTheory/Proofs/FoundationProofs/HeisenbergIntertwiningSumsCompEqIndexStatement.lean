import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_intertwining_sums_comp_eq_index : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → idx B A = idx A B ∧ ∀ v, Fixes W A v → sumOp W B A (sumOp W A B v) = (idx A B : ℂ) • v := by
  first | exact @GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul | exact GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul | (intros; apply GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul <;> assumption)
