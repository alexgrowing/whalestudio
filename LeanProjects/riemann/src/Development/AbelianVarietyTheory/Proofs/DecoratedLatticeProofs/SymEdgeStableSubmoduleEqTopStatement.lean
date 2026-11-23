import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymEdgeStableSubmoduleEqTop
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symEdge_stable_submodule_eq_top : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → ∀ (a : Fin n → Fin n → k), (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ (V : Submodule k (Fin n → k)), V ≠ ⊥ → (∀ w ∈ V, (fun j => ∑ i, if symEdge ρ κ i j then a i j * w i else 0) ∈ V) → (∀ i j : Fin n, i < j → ¬(ρ ≤ i.val ∧ i.val < ρ + κ ∧ j.val = ρ + κ) → ∀ w ∈ V, Pi.single i (w j) ∈ V) → V = ⊤ := by
  first | exact @GlobalTheory.symEdge_span_eq_top | exact GlobalTheory.symEdge_span_eq_top | (intros; apply GlobalTheory.symEdge_span_eq_top <;> assumption)
