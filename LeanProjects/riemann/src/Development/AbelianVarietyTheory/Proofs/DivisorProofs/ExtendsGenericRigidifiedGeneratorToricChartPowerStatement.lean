import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsGenericRigidifiedGeneratorToricChartPower
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullCubicalOfGenericOfExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendsGenericRigidifiedGenerator_toricChartPowerSeriesRing : ∀ (k : Type) [Field k] (m n : ℕ), GlobalTheory.ChartCubExt.ExtendGenAt (ChartRing k m n) (FractionRing (ChartRing k m n)) := by
  first | exact @GlobalTheory.ChartCubExt.extendGenAt_chartRing | exact GlobalTheory.ChartCubExt.extendGenAt_chartRing | (intros; apply GlobalTheory.ChartCubExt.extendGenAt_chartRing <;> assumption)
