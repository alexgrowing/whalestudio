import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictUpperMemClosureTransvection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_strictUpper_mem_closure_transvection : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, b ≤ a → c a b = 0) → 1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  first | exact @GlobalTheory.UpperTransvection.upper_mem_closure | exact GlobalTheory.UpperTransvection.upper_mem_closure | (intros; apply GlobalTheory.UpperTransvection.upper_mem_closure <;> assumption)
