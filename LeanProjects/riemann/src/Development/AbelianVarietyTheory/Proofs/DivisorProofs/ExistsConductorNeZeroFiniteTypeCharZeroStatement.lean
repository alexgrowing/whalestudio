import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConductorNeZeroFiniteTypeCharZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conductor_ne_zero_finiteType_charZero : ∀ (K R B : Type) [Field K] [CharZero K] [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] [CommRing B] [IsDomain B] [Algebra R B], Function.Injective (algebraMap R B) → ∃ c : R, c ≠ 0 ∧ ∀ x : B, IsIntegral R x → (∃ r s : R, r ≠ 0 ∧ algebraMap R B r * x = algebraMap R B s) → ∃ s : R, algebraMap R B c * x = algebraMap R B s := by
  first | exact @GlobalTheory.exists_ne_zero_mul_mem_of_isIntegral_of_fraction | exact GlobalTheory.exists_ne_zero_mul_mem_of_isIntegral_of_fraction | (intros; apply GlobalTheory.exists_ne_zero_mul_mem_of_isIntegral_of_fraction <;> assumption)
