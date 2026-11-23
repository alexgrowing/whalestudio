import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCellOfLeadingMinors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cell_of_leading_minors : ∀ {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (w : Equiv.Perm (Fin m)), (∀ (k : ℕ) (hk : k ≤ m), IsUnit ((M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det) → ∃ a, GlobalTheory.ShFam.Cell.InCell M w a := by
  first | exact @GlobalTheory.ShFam.Cell.exists_inCell_of_leadingMinors_isUnit | exact GlobalTheory.ShFam.Cell.exists_inCell_of_leadingMinors_isUnit | (intros; apply GlobalTheory.ShFam.Cell.exists_inCell_of_leadingMinors_isUnit <;> assumption)
