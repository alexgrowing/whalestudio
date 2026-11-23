import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzPartitionOfUnityLattice
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartz_partition_of_unity_lattice : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by
  first | exact @GlobalTheory.exists_schwartz_hasCompactSupport_latticeTranslates_sum_one | exact GlobalTheory.exists_schwartz_hasCompactSupport_latticeTranslates_sum_one | (intros; apply GlobalTheory.exists_schwartz_hasCompactSupport_latticeTranslates_sum_one <;> assumption)
