import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaFreeRankSqEquivMatrixOverLocal
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.azumaya_free_rank_sq_equiv_matrix_over_local : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.AzumayaLocal.azumaya_local_matrix) | (exact GlobalTheory.AzumayaLocal.azumaya_local_matrix) | (intros; apply GlobalTheory.AzumayaLocal.azumaya_local_matrix  <;> assumption)
