import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfForallHeightOneLocalizationIntegrallyClosed
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_forall_heightOne_localization_integrallyClosed : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (z : K), (∀ Q : Ideal A, Q.IsPrime → Q.height = 1 → ∃ r c : A, r ∉ Q ∧ algebraMap A K r * z = algebraMap A K c) → ∃ c : A, z = algebraMap A K c := by
  first | (exact @GlobalTheory.NormalHeightOne.mem_of_forall_height_eq_one) | (exact GlobalTheory.NormalHeightOne.mem_of_forall_height_eq_one) | (intros; apply GlobalTheory.NormalHeightOne.mem_of_forall_height_eq_one <;> assumption)
