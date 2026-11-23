import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRoo
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots : ∀ (A : Type) [CommRing A] [IsDomain A], AIC A → IsAlgClosed (FractionRing A) := by
  first | (exact @GlobalTheory.isAlgClosed_fractionRing_of_AIC) | (exact GlobalTheory.isAlgClosed_fractionRing_of_AIC) | (intros; apply GlobalTheory.isAlgClosed_fractionRing_of_AIC  <;> assumption)
