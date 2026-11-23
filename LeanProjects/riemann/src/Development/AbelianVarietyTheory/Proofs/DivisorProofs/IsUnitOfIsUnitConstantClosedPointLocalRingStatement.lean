import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfIsUnitConstantClosedPointLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_of_isUnit_constant_closedPoint_localRing : ∀ (V : Type) [CommRing V] [IsLocalRing V] (a : V), IsUnit (Geo.Tor.cst (𝟙 (Sp V)) (closedPoint V) a) → IsUnit a := by
  first | exact @GlobalTheory.unit_of_isUnit_cst_closedPoint | exact GlobalTheory.unit_of_isUnit_cst_closedPoint | (intros; apply GlobalTheory.unit_of_isUnit_cst_closedPoint <;> assumption)
