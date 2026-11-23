import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationIntegralClosureArtinianReducedDomain
import Mathlib
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
theorem _root_.GlobalTheory.T.localization_integralClosure_artinian_reduced_domain : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [IsArtinianRing A] [IsReduced A]
    (Q : Ideal (integralClosure R A)) [Q.IsPrime],
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  first | exact @GlobalTheory.localization_integralClosure_isDomain_isIntegrallyClosed | exact GlobalTheory.localization_integralClosure_isDomain_isIntegrallyClosed | (intros; apply GlobalTheory.localization_integralClosure_isDomain_isIntegrallyClosed <;> assumption)
