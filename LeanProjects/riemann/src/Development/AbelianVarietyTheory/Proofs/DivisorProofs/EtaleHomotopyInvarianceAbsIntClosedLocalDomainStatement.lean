import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsIntClosedLocalDomain
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_absIntClosedLocalDomain : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : T →+* Polynomial T)) (tw q i) := by
  first | (exact @GlobalTheory.EtC.HtpyLine.htpy_AIC) | (exact GlobalTheory.EtC.HtpyLine.htpy_AIC) | (intros; apply GlobalTheory.EtC.HtpyLine.htpy_AIC  <;> assumption)
