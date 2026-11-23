import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactOpenSubgroupMem
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_open_subgroup_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (x : Fin n → k), ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ x ∈ A := by
  first | exact @GlobalTheory.CompanionTheory.LatticePoint.exists_compact_open_addSubgroup_mem | exact GlobalTheory.CompanionTheory.LatticePoint.exists_compact_open_addSubgroup_mem | (intros; apply GlobalTheory.CompanionTheory.LatticePoint.exists_compact_open_addSubgroup_mem <;> assumption)
