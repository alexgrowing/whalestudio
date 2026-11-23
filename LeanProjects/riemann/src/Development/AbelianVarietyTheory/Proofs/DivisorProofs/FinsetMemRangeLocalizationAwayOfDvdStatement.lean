import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsetMemRangeLocalizationAwayOfDvd
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finset_mem_range_localization_away_of_dvd : ∀ (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] (F : Finset (Localization.AtPrime 𝔭)), ∃ s ∉ 𝔭, ∀ (c : R), s ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭, κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) → ∀ x ∈ F, x ∈ κ.range := by
  first | exact @GlobalTheory.finset_mem_range_of_away_dvd | exact GlobalTheory.finset_mem_range_of_away_dvd | (intros; apply GlobalTheory.finset_mem_range_of_away_dvd <;> assumption)
