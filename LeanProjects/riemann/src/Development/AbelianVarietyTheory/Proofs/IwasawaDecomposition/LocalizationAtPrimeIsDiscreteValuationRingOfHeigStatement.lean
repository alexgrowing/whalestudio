import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeig
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiscreteValuationRing_localization_of_height_eq_one' : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime], q.height = 1 → IsDiscreteValuationRing (Localization.AtPrime q) := by
  first | exact @GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one | exact GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one | (intros; apply GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one <;> assumption)
