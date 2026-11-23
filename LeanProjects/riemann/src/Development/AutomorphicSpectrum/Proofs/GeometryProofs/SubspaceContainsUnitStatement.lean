import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubspaceContainsUnit
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subspace_contains_unit : ∀ (k : Type) [Field k] [IsAlgClosed k] (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R]
    (U : Submodule k R), (∀ x : R →ₐ[k] k, ∃ t ∈ U, x t ≠ 0) → ∃ w ∈ U, IsUnit w := by
  first | exact @GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point | exact GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point | (intros; apply GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point <;> assumption)
