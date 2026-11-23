import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedSubgroupFiniteCosets
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
open Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_subgroup_finite_cosets : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] L →
    ∀ (n : ℕ) (B : Subgroup (GL (Fin n) L)) (c : ℝ),
      (∀ z ∈ B, ∀ i j, ‖((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ c) →
      ∃ T : Finset (GL (Fin n) L), (∀ t ∈ T, t ∈ B) ∧ ∀ z ∈ B, ∃ t ∈ T, t⁻¹ * z ∈ GlobalTheory.LKLoc.KintK p L n := by
  first | (exact @GlobalTheory.LKLoc.exists_finset_inv_mul_mem_KintK) | (exact GlobalTheory.LKLoc.exists_finset_inv_mul_mem_KintK) | (intros; apply GlobalTheory.LKLoc.exists_finset_inv_mul_mem_KintK <;> assumption)
