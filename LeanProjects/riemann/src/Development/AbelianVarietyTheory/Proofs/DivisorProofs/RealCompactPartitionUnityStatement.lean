import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealCompactPartitionUnity
import Mathlib
open MeasureTheory Filter Topology
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_compact_partition_unity : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    ∃ ψ : SchwartzMap V ℂ, HasCompactSupport (ψ : V → ℂ) ∧ (∀ x, starRingEnd ℂ (ψ x) = ψ x) ∧
      ∃ v : (Fin (Module.finrank ℝ V) → ℤ) → V, (∀ x, HasSum (fun j => ψ (x - v j)) 1) ∧
        (∀ R : ℝ, {j | ‖v j‖ ≤ R}.Finite) ∧ ∃ M : ℕ, Summable (fun j => ((1 + ‖v j‖) ^ M)⁻¹) := by
  first | exact @GlobalTheory.LatticePartition.exists_lattice_partition | exact GlobalTheory.LatticePartition.exists_lattice_partition | (intros; apply GlobalTheory.LatticePartition.exists_lattice_partition <;> assumption)
