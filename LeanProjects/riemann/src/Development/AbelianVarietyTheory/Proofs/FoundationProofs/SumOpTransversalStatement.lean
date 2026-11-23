import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ B → (∀ v, Fixes W A v → ∀ (ι : Type) [Fintype ι] (f : ι → X), (∀ i, f i ∈ B) → (∀ b ∈ B, ∃! i, b - f i ∈ A) → sumOp W A B v = ∑ i, W (f i) v ∧ idx A B = Fintype.card ι) ∧ (idx A B ≠ 0 → (∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧ ∀ b ∈ B, ∃! i, b - f i ∈ A) ∧ (∀ v, Fixes W A v → Fixes W B (sumOp W A B v)) ∧ ∀ (c : ℂ) v, sumOp W A B (c • v) = c • sumOp W A B v) ∧ (B ≤ A → idx A B = 1 ∧ ∀ v, Fixes W A v → sumOp W A B v = v) := by
  first | exact @GlobalTheory.FinWeil.sumOp_transversal | exact GlobalTheory.FinWeil.sumOp_transversal | (intros; apply GlobalTheory.FinWeil.sumOp_transversal <;> assumption)
