import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedFirstIsometricDualO1
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_first_isometric_dual_O1 : (VMetric.grLB TautFlag.flag 0 TautFlag.stdH.cInf).Isometric (ProjSpace.hermitianTwistingSheaf ℤ 1).dual := by
  first | exact @GlobalTheory.TautFlag.isometric_grLB_zero | exact GlobalTheory.TautFlag.isometric_grLB_zero | (intros; apply GlobalTheory.TautFlag.isometric_grLB_zero <;> assumption)
