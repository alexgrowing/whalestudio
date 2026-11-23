import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticNormHeckeCharRamifiedBelowRamifiedPrime
import Mathlib
open NumberField IsDedekindDomain Formalism.L2.Host UpperTheory.V.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_norm_hecke_char_ramified_below_ramified_prime : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M], Module.finrank K M = 2 → ∀ η : HChar K, IsNormChar M η → ∀ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal → ¬ η.UnrAt (w.under (𝓞 K)) := by
  first | exact @GlobalTheory.QuadNormRam.not_unrAt_of_ramified | exact GlobalTheory.QuadNormRam.not_unrAt_of_ramified | (intros; apply GlobalTheory.QuadNormRam.not_unrAt_of_ramified <;> assumption)
