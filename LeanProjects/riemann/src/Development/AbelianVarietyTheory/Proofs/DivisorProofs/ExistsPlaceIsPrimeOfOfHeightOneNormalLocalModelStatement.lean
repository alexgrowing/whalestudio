import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceIsPrimeOfOfHeightOneNormalLocalModel
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open GlobalTheory GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_isPrimeOf_of_height_one_normal_localModel : ∀ {K : Type} [Field K] (cK : ℂ →+* K) (R : Subring K), IsLocModel cK R → IsIntegrallyClosed R →
    ∀ p : Ideal R, p.IsPrime → p.height = 1 →
    ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ g ∉ p) := by
  first | exact @GlobalTheory.FieldPair.exists_place_isPrimeOf_of_height_eq_one | exact GlobalTheory.FieldPair.exists_place_isPrimeOf_of_height_eq_one | (intros; apply GlobalTheory.FieldPair.exists_place_isPrimeOf_of_height_eq_one <;> assumption)
