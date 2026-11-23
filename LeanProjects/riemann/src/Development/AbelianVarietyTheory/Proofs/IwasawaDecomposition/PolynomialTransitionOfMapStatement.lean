import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialTransitionOfMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_transition_of_map : PolMapSt → PolTransSt := by
  first | exact @GlobalTheory.TorRef.polTransSt_of_polMapSt | exact GlobalTheory.TorRef.polTransSt_of_polMapSt | (intros; apply GlobalTheory.TorRef.polTransSt_of_polMapSt <;> assumption)
