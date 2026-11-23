import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishAtPlaces
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_sums_vanish_at_places : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ D : ℕ, IsArithVar (mCoordIdeal y) (D + 1) → ∀ (p : Nat.Primes) (N : ℕ) (x : Fin N → K → ℤ), (AtPlacesOver A Ω p fun O _ _ _ _ => PowerSumsVanish (pointIdeal O y) D x) → PowerSumsVanish (extTo (ZP p) (mCoordIdeal y)) D x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.powerSumsVanish_extTo_of_atPlacesOver | exact GlobalTheory.CompanionTheory.Ar.Num.powerSumsVanish_extTo_of_atPlacesOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.powerSumsVanish_extTo_of_atPlacesOver <;> assumption)
