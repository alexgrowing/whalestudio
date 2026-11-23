import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjOfCharpolyLocal
open Polynomial Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_of_charpoly_eq_of_separable_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y Y' : Matrix (Fin n) (Fin n) R), Y.charpoly = Y'.charpoly → Y.charpoly.Separable → ∃ g : GL (Fin n) R, Y' = (g⁻¹ : GL (Fin n) R).val * Y * g.val := by
  first | exact @GlobalTheory.ConjLocal.conj_of_charpoly_local | exact GlobalTheory.ConjLocal.conj_of_charpoly_local | (intros; apply GlobalTheory.ConjLocal.conj_of_charpoly_local <;> assumption)
