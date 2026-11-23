import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorOpenCompact
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_open_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ∧ IsCompact {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact | exact GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact | (intros; apply GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact <;> assumption)
