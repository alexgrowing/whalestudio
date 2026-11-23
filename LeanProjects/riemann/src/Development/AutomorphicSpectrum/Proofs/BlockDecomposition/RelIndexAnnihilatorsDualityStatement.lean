import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexAnnihilatorsDuality
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_annihilators_duality : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A₀ A P₀ P : AddSubgroup (Fin n → k)), IsCompact (A₀ : Set (Fin n → k)) → IsOpen (A₀ : Set (Fin n → k)) → IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → A₀ ≤ A → (∀ ξ, ξ ∈ P₀ ↔ ∀ a ∈ A₀, ψ (ξ ⬝ᵥ a) = 1) → (∀ ξ, ξ ∈ P ↔ ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1) → P.relIndex P₀ = A₀.relIndex A := by
  first | exact @GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq | exact GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq | (intros; apply GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq <;> assumption)
