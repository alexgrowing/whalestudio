import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroLocusSectionPullbackExtends
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_locus_section_pullback_extends : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (B : LB M.X), B.IsLB → ∀ t : (B.pull M.j).Sec, ∃ s : B.Sec, ∀ y : Y.X, M.j y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  first | exact @GlobalTheory.ModelSecExt.main | exact GlobalTheory.ModelSecExt.main | (intros; apply GlobalTheory.ModelSecExt.main <;> assumption)
