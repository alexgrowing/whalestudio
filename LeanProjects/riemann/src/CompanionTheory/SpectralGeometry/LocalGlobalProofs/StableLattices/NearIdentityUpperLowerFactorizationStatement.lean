import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.near_identity_upper_lower_factorization : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ), 0 ≤ r → r < 1 → ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) → ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧ (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation | exact GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation | (intros; apply GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation <;> assumption)
