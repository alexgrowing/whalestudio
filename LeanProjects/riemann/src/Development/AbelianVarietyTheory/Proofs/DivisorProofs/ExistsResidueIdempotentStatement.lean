import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueIdempotent
import Mathlib
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_idempotent' : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ] [Nontrivial Λ], ∃ x : Λ, x * x - x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) ∧ (∀ y : Λ, ∃ c : A, x * y * x - c • x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ)) ∧ ∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * x * b i - 1 ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) := by
  first | (exact @GlobalTheory.AzumayaResidue.exists_residue_idempotent) | (exact GlobalTheory.AzumayaResidue.exists_residue_idempotent) | (intros; apply GlobalTheory.AzumayaResidue.exists_residue_idempotent  <;> assumption)
