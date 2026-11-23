import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_zero_homogeneous_ratFunc_of_mul_lt : ∀ (k : Type) [Field k] [IsAlgClosed k] (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) (RatFunc k)),
  (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n → ∃ x : Fin n → RatFunc k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  first | exact @GlobalTheory.tsenLang_ratFunc | exact GlobalTheory.tsenLang_ratFunc | (intros; apply GlobalTheory.tsenLang_ratFunc <;> assumption)
