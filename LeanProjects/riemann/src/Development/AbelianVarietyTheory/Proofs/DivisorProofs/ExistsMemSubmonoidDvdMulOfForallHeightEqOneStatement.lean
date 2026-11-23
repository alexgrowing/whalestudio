import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSubmonoidDvdMulOfForallHeightEqOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_submonoid_dvd_mul_of_height_one : ∀ (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (S : Submonoid B), (0 : B) ∉ S → ∀ x y : B, y ≠ 0 →
    (∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → y ∈ Q → Disjoint (S : Set B) (Q : Set B) →
      ∃ t ∉ Q, y ∣ t * x) → ∃ u ∈ S, y ∣ u * x := by
  first | (exact @GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one) | (exact GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one) | (intros; apply GlobalTheory.exists_mem_submonoid_dvd_mul_of_forall_height_eq_one <;> assumption)
