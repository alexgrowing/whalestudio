import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeMulLeftIdempotentGroupAlgebra
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_range_mulLeft_idempotent_groupAlgebra : ∀ (K H : Type) [Field K] [CharZero K] [Group H] [Finite H] (a : MonoidAlgebra K H), a * a = a → ((finrank K (LinearMap.range (LinearMap.mulLeft K a)) : ℕ) : K) = (Nat.card H : K) * a.coeff 1 := by
  first | exact @GlobalTheory.BadCount.finrank_range_mulLeft_idem | exact GlobalTheory.BadCount.finrank_range_mulLeft_idem | (intros; apply GlobalTheory.BadCount.finrank_range_mulLeft_idem <;> assumption)
