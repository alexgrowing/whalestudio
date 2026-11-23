import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupAddSubgroup
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_sup_addSubgroup : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by
  first | exact @GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup | exact GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup | (intros; apply GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup <;> assumption)
