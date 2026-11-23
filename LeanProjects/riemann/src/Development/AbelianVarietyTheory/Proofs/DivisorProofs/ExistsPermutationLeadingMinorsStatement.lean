import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermutationLeadingMinors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_permutation_leading_minors : ∀ {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R), IsUnit M.det → ∃ w : Equiv.Perm (Fin m), ∀ (k : ℕ) (hk : k ≤ m), IsUnit ((M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
  first | exact @GlobalTheory.exists_perm_isUnit_leading_minors_localRing | exact GlobalTheory.exists_perm_isUnit_leading_minors_localRing | (intros; apply GlobalTheory.exists_perm_isUnit_leading_minors_localRing <;> assumption)
