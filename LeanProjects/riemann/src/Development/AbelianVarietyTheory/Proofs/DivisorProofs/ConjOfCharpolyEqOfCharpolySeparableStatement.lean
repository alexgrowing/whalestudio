import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjOfCharpolyEqOfCharpolySeparable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclicVectorOfSeparableCharpoly
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_of_charpoly_eq_of_charpoly_separable : ∀ (R : Type) [Field R] (m : ℕ) (N U : Matrix (Fin m) (Fin m) R), N.charpoly = U.charpoly → N.charpoly.Separable → ∃ P : GL (Fin m) R, N * P.val = P.val * U := by
  first | exact @GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable | exact GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable | (intros; apply GlobalTheory.SimSep.conj_of_charpoly_eq_of_separable <;> assumption)
