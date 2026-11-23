import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleClearDenominator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adele_clear_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ a : Af E, ∃ m : E, m ≠ 0 ∧ algebraMap E (Af E) m * a ∈ hatO c := by
  first | exact @GlobalTheory.CMVal.IntMult.exists_mul_mem_hatO | exact GlobalTheory.CMVal.IntMult.exists_mul_mem_hatO | (intros; apply GlobalTheory.CMVal.IntMult.exists_mul_mem_hatO <;> assumption)
