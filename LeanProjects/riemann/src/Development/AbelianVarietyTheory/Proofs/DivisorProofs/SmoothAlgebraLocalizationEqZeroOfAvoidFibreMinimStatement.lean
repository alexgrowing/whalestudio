import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
import Mathlib
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_algebra_localization_eq_zero_of_avoid_fibre_minimal : ∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  first | exact @GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero | exact GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero | (intros; apply GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero <;> assumption)
