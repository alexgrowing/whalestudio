import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMultipleMemSublattice
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_multiple_mem_sublattice : ∀ (n : ℕ) (Λ Λ₂ M : Submodule ℤ (Fin n → ℂ)), DiscreteTopology Λ → DiscreteTopology Λ₂ → Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → Submodule.span ℝ (Λ₂ : Set (Fin n → ℂ)) = ⊤ → M ≤ Λ → Module.rank ℤ Λ₂ ≤ Module.rank ℤ M → ∀ w ∈ Λ, ∃ k : ℤ, k ≠ 0 ∧ k • w ∈ M := by
  first | exact @GlobalTheory.sublattice_of_full_rank_quotient_torsion | exact GlobalTheory.sublattice_of_full_rank_quotient_torsion | (intros; apply GlobalTheory.sublattice_of_full_rank_quotient_torsion <;> assumption)
