import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotCongruentZeroIntCastMulPrimePow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_congruent_zero_intCast_mul_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (t k : ℕ) (d : ℤ), d ≠ 0 → |d| < (l : ℤ) ^ t → ¬ Cg (t + k) ((d : Qbar l) * ((l : ℕ) : Qbar l) ^ k) 0 := by
  first | exact @GlobalTheory.Ord2.IntNorm.not_cg_int_mul_pow | exact GlobalTheory.Ord2.IntNorm.not_cg_int_mul_pow | (intros; apply GlobalTheory.Ord2.IntNorm.not_cg_int_mul_pow <;> assumption)
