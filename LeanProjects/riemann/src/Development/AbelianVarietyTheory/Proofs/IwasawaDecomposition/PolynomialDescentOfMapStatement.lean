import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialDescentOfMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_descent_of_map : PolMapSt → PolDescSt := by
  first | exact @GlobalTheory.TorRef.polDescSt_of_polMapSt | exact GlobalTheory.TorRef.polDescSt_of_polMapSt | (intros; apply GlobalTheory.TorRef.polDescSt_of_polMapSt <;> assumption)
