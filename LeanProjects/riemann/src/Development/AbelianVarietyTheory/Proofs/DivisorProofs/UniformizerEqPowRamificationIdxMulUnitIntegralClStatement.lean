import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerEqPowRamificationIdxMulUnitIntegralCl
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_eq_pow_ramificationIdx_mul_unit_integralClosure : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D] (P : Ideal (integralClosure S L)) [P.IsMaximal], Irreducible π → algebraMap S (integralClosure S L) π ∈ P → ∃ ϖ : Localization.AtPrime P, Irreducible ϖ ∧ ∃ u : (Localization.AtPrime P)ˣ, algebraMap S (Localization.AtPrime P) π = ϖ ^ P.ramificationIdx S * (u : Localization.AtPrime P) := by
  first | (exact @GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit) | (exact GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit) | (intros; apply GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit  <;> assumption)
