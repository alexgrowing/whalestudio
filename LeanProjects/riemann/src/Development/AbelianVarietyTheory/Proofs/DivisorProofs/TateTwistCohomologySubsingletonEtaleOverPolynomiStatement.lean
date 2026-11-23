import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySubsingletonEtaleOverPolynomi
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_subsingleton_etale_over_polynomial_algClosed : ∀ (q : ℕ) [NeZero q] (K E : Type) [Field K] [IsAlgClosed K] [CommRing E] [Algebra (Polynomial K) E] [Algebra.Etale (Polynomial K) E], IsUnit (q : K) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp E) n i) := by
  first | (exact @GlobalTheory.EtAlgCD.etale_polynomial_cd_le_one) | (exact GlobalTheory.EtAlgCD.etale_polynomial_cd_le_one) | (intros; apply GlobalTheory.EtAlgCD.etale_polynomial_cd_le_one <;> assumption)
