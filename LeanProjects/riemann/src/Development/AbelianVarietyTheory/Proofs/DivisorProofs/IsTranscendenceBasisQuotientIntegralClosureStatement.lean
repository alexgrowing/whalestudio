import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisQuotientIntegralClosure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTranscendenceBasis_quotient_integralClosure' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (Q : Ideal B), Q.IsPrime → ∀ (t : A), (∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a)) → ∀ (m : ℕ) (y : Fin m → A), IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)) → ∀ y' : Fin m → B, (∀ j, (y' j : K) = algebraMap F K (y j)) → IsTranscendenceBasis k (fun j => Ideal.Quotient.mk Q (y' j)) := by
  first | (exact @GlobalTheory.isTranscendenceBasis_quotient_integralClosure) | (exact GlobalTheory.isTranscendenceBasis_quotient_integralClosure) | (intros; apply GlobalTheory.isTranscendenceBasis_quotient_integralClosure <;> assumption)
