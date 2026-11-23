import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingAtPrimeOfEtale
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgClosed_fractionRing_atPrime_of_etale' : ∀ (T E : Type) [CommRing T] [IsDomain T] [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime] [IsDomain (Localization.AtPrime P)], IsAlgClosed (FractionRing T) → IsAlgClosed (FractionRing (Localization.AtPrime P)) := by
  first | (exact @GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale) | (exact GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale) | (intros; apply GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale  <;> assumption)
