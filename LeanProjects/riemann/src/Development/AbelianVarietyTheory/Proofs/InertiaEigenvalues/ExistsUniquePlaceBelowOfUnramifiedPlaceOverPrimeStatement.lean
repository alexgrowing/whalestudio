import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniquePlaceBelowOfUnramifiedPlaceOverPrime
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_place_below_of_unramified_place_over_prime : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (l : ℕ), l.Prime → ∀ la : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt φ {la} → ∃ p : HeightOneSpectrum (𝓞 K), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below φ {la} = {p} ∧ ((l : ℕ) : 𝓞 K) ∈ p.asIdeal ∧ ∀ x : K, la.valuation L (φ x) = p.valuation K x := by
  first | exact @GlobalTheory.InertiaEigenvalues.UnramPlace.exists_place_below | exact GlobalTheory.InertiaEigenvalues.UnramPlace.exists_place_below | (intros; apply GlobalTheory.InertiaEigenvalues.UnramPlace.exists_place_below <;> assumption)
