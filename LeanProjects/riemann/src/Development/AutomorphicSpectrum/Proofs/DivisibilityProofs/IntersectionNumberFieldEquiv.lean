import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGenFibNef
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem intNumL_map_ringEquiv : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (F F' : Type) [Field F] [Field F'] (e : F ≃+* F') (V : Ideal (MRing ι F)) (l : List (K → ℤ)), intNumL F' (V.map (MvPolynomial.map (e : F →+* F'))) l = intNumL F V l := by
  intro K _ _ ι _ F F' _ _ e V l
  exact GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.GenFibNef.intNum_map e V l.get

end GlobalTheory.CompanionTheory.Ar.Num
