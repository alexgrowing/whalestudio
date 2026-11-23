import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberLocalCycle
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_number_local_cycle : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (p : Nat.Primes) (a : K → ℕ) (f : MRing ι ℤ), IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = D → vertAt p P f l = cycList (divCycle (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) f)) l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList | exact GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.vertAt_eq_cycList <;> assumption)
