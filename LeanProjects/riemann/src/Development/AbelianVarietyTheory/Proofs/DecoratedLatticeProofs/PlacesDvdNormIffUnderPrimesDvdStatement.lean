import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacesDvdNormIffUnderPrimesDvd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
open NumberField IsDedekindDomain Formalism.BasicNotions
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_dvd_norm_iff_under_primes_dvd : ∀ (D : Formalism.BasicNotions.D7) (π π' : 𝓞 D.host.E) (T : ℕ), (π' : D.host.E) = star (π : D.host.E) → π * π' = (T : 𝓞 D.host.E) → π ≠ 0 → ∀ x : HeightOneSpectrum (𝓞 D.host.F), (T : 𝓞 D.host.F) ∈ x.asIdeal ↔ ∃ w ∈ Formalism.L2.Col.divs π, w.under (𝓞 D.host.F) = x := by
  first | exact @GlobalTheory.NormPlaces.places_dvd_iff | exact GlobalTheory.NormPlaces.places_dvd_iff | (intros; apply GlobalTheory.NormPlaces.places_dvd_iff <;> assumption)
