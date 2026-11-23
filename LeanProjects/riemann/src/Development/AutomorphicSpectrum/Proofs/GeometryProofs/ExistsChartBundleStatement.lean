import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartBundle
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ), CoordTie ℤ ξ x → L.IsVB r ⊤ → ∃ W : ChartBundle ℤ x r E, L.IsChartOf x W.lat := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_chartBundle_of_isVB | exact GlobalTheory.CompanionTheory.Ar.exists_chartBundle_of_isVB | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_chartBundle_of_isVB <;> assumption)
