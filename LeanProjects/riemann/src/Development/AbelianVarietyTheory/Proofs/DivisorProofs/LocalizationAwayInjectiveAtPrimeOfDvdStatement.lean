import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayInjectiveAtPrimeOfDvd
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_away_injective_atPrime_of_dvd : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime], ∃ t ∉ 𝔭, ∀ (c : R), t ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭, κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) → Function.Injective κ := by
  first | exact @GlobalTheory.localization_away_injective_of_dvd | exact GlobalTheory.localization_away_injective_of_dvd | (intros; apply GlobalTheory.localization_away_injective_of_dvd <;> assumption)
