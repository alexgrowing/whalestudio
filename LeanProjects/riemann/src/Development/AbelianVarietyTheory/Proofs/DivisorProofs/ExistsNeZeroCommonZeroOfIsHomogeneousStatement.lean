import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroCommonZeroOfIsHomogeneous
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_common_zero_of_isHomogeneous' : ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (f : Fin r → MvPolynomial (Fin n) k), (∀ i, ∃ d, 0 < d ∧ (f i).IsHomogeneous d) → r < n → ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  first | exact @GlobalTheory.exists_ne_zero_common_zero_of_isHomogeneous | exact GlobalTheory.exists_ne_zero_common_zero_of_isHomogeneous | (intros; apply GlobalTheory.exists_ne_zero_common_zero_of_isHomogeneous <;> assumption)
