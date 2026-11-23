import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRealSpanEqConjFixedPrimeMulRelNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_span_eq_conjFixedPrime_mul_relNorm : ∀ (D : D7) (P : Ideal (𝓞 D.host.E)), P.IsPrime → P ≠ ⊥ → D.host.conj • P = P → ∃ (t : 𝓞 D.host.E) (B : Ideal (𝓞 D.host.E)), t ≠ 0 ∧ D.host.conj (t : D.host.E) = t ∧ Ideal.span {t} = P * B * (D.host.conj • B) := by
  first | exact @GlobalTheory.FixedPrimeNorm.exists_span_eq_prime_mul_norm | exact GlobalTheory.FixedPrimeNorm.exists_span_eq_prime_mul_norm | (intros; apply GlobalTheory.FixedPrimeNorm.exists_span_eq_prime_mul_norm <;> assumption)
