import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalizationModelOverPlace
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_model_over_place : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ D : ℕ, IsArithVar (mCoordIdeal y) (D + 1) → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], pointIdeal O y = (pointIdeal A y).map (MvPolynomial.map (algebraMap A O)) ∧ IsModelOver (pointIdeal O y) D ∧ ∀ (ϖ : O), Irreducible ϖ → ∀ (σ : Type) (S : Finset Nat.Primes) (T : LocPair ι ℤ σ), T.IsVertOff (mCoordIdeal y) S → (T.map (Int.castRingHom O)).IsVert (pointIdeal O y) ϖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.pl_model | exact GlobalTheory.CompanionTheory.Ar.Num.pl_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.pl_model <;> assumption)
