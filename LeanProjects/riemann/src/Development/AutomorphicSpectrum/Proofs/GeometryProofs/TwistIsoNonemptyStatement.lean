import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistIsoNonempty
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_iso_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H), Nonempty (TwIso D g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.tw_iso_nonempty | exact GlobalTheory.CompanionTheory.Ar.tw_iso_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.tw_iso_nonempty <;> assumption)
