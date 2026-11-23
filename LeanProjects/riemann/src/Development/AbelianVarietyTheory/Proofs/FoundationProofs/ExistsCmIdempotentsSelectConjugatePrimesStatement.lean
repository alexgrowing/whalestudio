import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_idempotents_select_conjugate_primes : ∀ (D : D7), ∃ e : ℕ → 𝓞 D.host.E, (∀ N m : ℕ, 0 < N → 0 < m → (N : 𝓞 D.host.E) ∣ e (N * m) - e N) ∧ (∀ N : ℕ, 0 < N → (N : 𝓞 D.host.E) ∣ e N * e N - e N ∧ (N : 𝓞 D.host.E) ∣ e N * (D.host.conj • e N)) ∧ ∀ q k : ℕ, q.Prime → (InertQ D q → ((q ^ k : ℕ) : 𝓞 D.host.E) ∣ e (q ^ k) + D.host.conj • e (q ^ k)) ∧ (¬ InertQ D q → ((q ^ k : ℕ) : 𝓞 D.host.E) ∣ 1 - (e (q ^ k) + D.host.conj • e (q ^ k))) := by
  first | exact @GlobalTheory.SelectIdem.exists_select_idem | exact GlobalTheory.SelectIdem.exists_select_idem | (intros; apply GlobalTheory.SelectIdem.exists_select_idem <;> assumption)
