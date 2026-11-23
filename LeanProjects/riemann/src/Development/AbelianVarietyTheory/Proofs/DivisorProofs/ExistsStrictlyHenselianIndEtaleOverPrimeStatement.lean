import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianIndEtaleOverPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strictlyHenselian_indEtale_over_prime : ∀ (A : Type) [CommRing A] (p : Ideal A) [p.IsPrime], ∃ (O : Type) (_ : CommRing O) (_ : Algebra A O) (_ : IsLocalRing O), SH O ∧ IndEt A O ∧ (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p := by
  first | (exact @GlobalTheory.StrictHensPrime.exists_sh_indEt) | (exact GlobalTheory.StrictHensPrime.exists_sh_indEt) | (intros; apply GlobalTheory.StrictHensPrime.exists_sh_indEt  <;> assumption)
