import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoAnyRing
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_degree_two_any_ring : PrimitiveExtendedDegTwoVanish := by
  first | exact @GlobalTheory.Obs.primE2_any_ring | exact GlobalTheory.Obs.primE2_any_ring | (intros; apply GlobalTheory.Obs.primE2_any_ring <;> assumption)
