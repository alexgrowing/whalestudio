import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRowPermLeadingMinorsNotMem
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_leadingMinors_not_mem : ∀ (R : Type) [CommRing R] (n : ℕ) (T : Matrix (Fin n) (Fin n) R) (p : Ideal R), p.IsPrime → T.det ∉ p → ∃ w : Equiv.Perm (Fin n), ∀ (k : ℕ) (hk : k ≤ n), ((T.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ∉ p := by
  first | exact @GlobalTheory.exists_rowPerm_leadingMinors_not_mem | exact GlobalTheory.exists_rowPerm_leadingMinors_not_mem | (intros; apply GlobalTheory.exists_rowPerm_leadingMinors_not_mem <;> assumption)
