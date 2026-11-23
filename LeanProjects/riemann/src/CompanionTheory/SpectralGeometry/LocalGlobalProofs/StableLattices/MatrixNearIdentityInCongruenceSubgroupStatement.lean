import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroup
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_near_identity_in_congruence_subgroup : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r < 1 → ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) → ∃ k ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, (k : Matrix (Fin n) (Fin n) L) = A := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries | exact GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries | (intros; apply GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries <;> assumption)
