import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsManyBoundedByPow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearIndependent_bounded_by_pow_of_transcendental : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ t : F, Transcendental k t → ∃ c : ℕ, ∀ N : ℕ, ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ ((N : ℤ) - c) * Module.finrank k⟮t⟯ F ≤ n ∧ ∀ (i : Fin n) (v : Place k F), v.1 (f i) ≤ max 1 (v.1 t) ^ N := by
  first | exact @GlobalTheory.Nef.exists_many_bounded_by_pow | exact GlobalTheory.Nef.exists_many_bounded_by_pow | (intros; apply GlobalTheory.Nef.exists_many_bounded_by_pow <;> assumption)
