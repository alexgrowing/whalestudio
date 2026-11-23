import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSecondIsometricO1
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_second_isometric_O1 : (VMetric.grLB TautFlag.flag 1 TautFlag.stdH.cInf).Isometric (ProjSpace.hermitianTwistingSheaf ℤ 1) := by
  first | exact @GlobalTheory.TautFlag.isometric_grLB_one | exact GlobalTheory.TautFlag.isometric_grLB_one | (intros; apply GlobalTheory.TautFlag.isometric_grLB_one <;> assumption)
