import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_local_ring_normal_domain : ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsDomain T ∧ IsIntegrallyClosed T := by
  first | exact @GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing | exact GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing | (intros; apply GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing <;> assumption)
