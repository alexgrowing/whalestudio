import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalImpliesGeometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_local_implies_geometric : RegLocSt → GeoSt := by
  first | exact @GlobalTheory.DetHT.geoSt_of_regLocSt | exact GlobalTheory.DetHT.geoSt_of_regLocSt | (intros; apply GlobalTheory.DetHT.geoSt_of_regLocSt <;> assumption)
