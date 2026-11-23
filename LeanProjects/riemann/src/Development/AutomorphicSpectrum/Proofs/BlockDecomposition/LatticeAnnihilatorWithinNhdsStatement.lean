import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeAnnihilatorWithinNhds
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_annihilator_within_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (U : Set (Fin n → k)), U ∈ nhds (0 : Fin n → k) → ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset | exact GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset | (intros; apply GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset <;> assumption)
