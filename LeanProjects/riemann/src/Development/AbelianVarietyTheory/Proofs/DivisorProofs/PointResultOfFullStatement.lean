import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointResultOfFull
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_result_of_full : FullSt → PtSt := by
  first | exact @GlobalTheory.HalfGeo.PointClauses.ptSt_of_fullSt | exact GlobalTheory.HalfGeo.PointClauses.ptSt_of_fullSt | (intros; apply GlobalTheory.HalfGeo.PointClauses.ptSt_of_fullSt <;> assumption)
