import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergSumCompOfAdjacentOfInfEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergSum_comp_of_adjacent_of_inf_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → A ⊓ C = B ⊓ C → ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = lam (idx A B) • sumOp W A C v := by
  first | exact @GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq | exact GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq | (intros; apply GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq <;> assumption)
