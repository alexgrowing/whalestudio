import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCosetRepresentatives
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_coset_representatives : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by
  first | exact @GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main | exact GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main | (intros; apply GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main <;> assumption)
