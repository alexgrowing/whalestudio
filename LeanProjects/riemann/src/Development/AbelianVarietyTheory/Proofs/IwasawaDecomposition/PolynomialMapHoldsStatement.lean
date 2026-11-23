import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMapHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_map_holds : PolMapSt := by
  first | exact @GlobalTheory.TorRef.polMapSt | exact GlobalTheory.TorRef.polMapSt | (intros; apply GlobalTheory.TorRef.polMapSt <;> assumption)
