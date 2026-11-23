import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitOfDvrUnit
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_unit_of_dvr_unit : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] (𝔭 : PrimeSpectrum A),
    𝔭.asIdeal.height = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (iT : Localization.AtPrime 𝔭.asIdeal →+* V), Function.Injective iT → IsLocalHom iT → ∀ a b : A,
    (∃ w : Vˣ, iT (algebraMap A _ a) = iT (algebraMap A _ b) * w) →
    ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ, (u : Localization.AtPrime 𝔭.asIdeal) * algebraMap A _ b = algebraMap A _ a := by
  first | exact @GlobalTheory.unitMultiple_descends_of_height_eq_one | exact GlobalTheory.unitMultiple_descends_of_height_eq_one | (intros; apply GlobalTheory.unitMultiple_descends_of_height_eq_one <;> assumption)
