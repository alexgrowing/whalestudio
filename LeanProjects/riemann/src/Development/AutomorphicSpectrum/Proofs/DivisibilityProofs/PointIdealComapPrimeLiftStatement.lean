import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PointIdealComapPrimeLift
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_ideal_comap_prime_lift : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → (pointIdeal A y).comap (MvPolynomial.map (Int.castRingHom A)) = mCoordIdeal y ∧ (∀ W : Ideal (MRing ι ℤ), W.IsPrime → IsRelevant W → mCoordIdeal y ≤ W → ∃! W' : Ideal (MRing ι A), W'.IsPrime ∧ pointIdeal A y ≤ W' ∧ W'.comap (MvPolynomial.map (Int.castRingHom A)) = W) ∧ ∀ (f : MRing ι ℤ) (W' : Ideal (MRing ι A)), W'.IsPrime → IsRelevant W' → pointIdeal A y ≤ W' → divCycle (pointIdeal A y) (MvPolynomial.map (Int.castRingHom A) f) W' = divCycle (mCoordIdeal y) f (W'.comap (MvPolynomial.map (Int.castRingHom A))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.pl_corr | exact GlobalTheory.CompanionTheory.Ar.Num.pl_corr | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.pl_corr <;> assumption)
