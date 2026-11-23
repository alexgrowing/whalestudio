import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineDegree
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_result_of_integrality : IntSt → PointSt := by
  first | exact @GlobalTheory.HalfGeo.pointSt_of_intSt | exact GlobalTheory.HalfGeo.pointSt_of_intSt | (intros; apply GlobalTheory.HalfGeo.pointSt_of_intSt <;> assumption)
