import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactLatticeContaining
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_compact_lattice_containing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ K ⊆ A := by
  first | exact @GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup | exact GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup | (intros; apply GlobalTheory.CompanionTheory.LocalLattice.exists_compact_open_addSubgroup <;> assumption)
