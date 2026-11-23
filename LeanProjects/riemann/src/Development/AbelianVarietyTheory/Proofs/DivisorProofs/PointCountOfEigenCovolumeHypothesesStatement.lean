import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCountOfEigenCovolumeHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_count_of_eigen_covolume_hypotheses : BridgeSt → EigSt → CovolSt → PointSt := by
  first | exact @GlobalTheory.DetHT.pointSt_of | exact GlobalTheory.DetHT.pointSt_of | (intros; apply GlobalTheory.DetHT.pointSt_of <;> assumption)
