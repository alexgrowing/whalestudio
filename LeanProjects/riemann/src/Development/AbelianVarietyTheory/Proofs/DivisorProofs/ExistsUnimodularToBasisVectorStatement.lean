import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularToBasisVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open GlobalTheory.TriFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_to_basis_vector : ∀ {R : Type} [CommRing R] {r : ℕ} (a : Fin (r+1) → R) (l0 : Fin (r+1)), IsUnit (a l0) → ∃ Q : GL (Fin (r+1)) R, (Q : Matrix (Fin (r+1)) (Fin (r+1)) R).mulVec a = (Pi.single 0 1 : Fin (r+1) → R) := by
  first | exact @GlobalTheory.column_unit_entry_to_first_basis_vector | exact GlobalTheory.column_unit_entry_to_first_basis_vector | (intros; apply GlobalTheory.column_unit_entry_to_first_basis_vector <;> assumption)
