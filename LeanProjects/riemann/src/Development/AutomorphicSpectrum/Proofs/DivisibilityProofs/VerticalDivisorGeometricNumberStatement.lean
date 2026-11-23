import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalDivisorGeometricNumber
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_divisor_geometric_number : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (a : K → ℕ) (f : MRing ι ℤ), IsMultiHomog f a → f ∉ P → ∀ W, divCycle P f W ≠ 0 → ∀ (p : ℕ) [Fact p.Prime], (C (p : ℤ) : MRing ι ℤ) ∈ W → charOf W = p ∧ ¬ IsHorizontal W ∧ ∀ L : Fin D → K → ℤ, geoNum D W L = intNum (ZMod p) (extTo (ZMod p) W) L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.GeoNumFp.geoNum_eq_intNum | exact GlobalTheory.CompanionTheory.Ar.Num.GeoNumFp.geoNum_eq_intNum | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.GeoNumFp.geoNum_eq_intNum <;> assumption)
