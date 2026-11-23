import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalSiegelCompactificationExists
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimalSiegelCompactification_exists : GlobalTheory.SiegJoin.MinSt5 := by
  first | exact @GlobalTheory.SiegMinTop.minSt5 | exact GlobalTheory.SiegMinTop.minSt5 | (intros; apply GlobalTheory.SiegMinTop.minSt5 <;> assumption)
