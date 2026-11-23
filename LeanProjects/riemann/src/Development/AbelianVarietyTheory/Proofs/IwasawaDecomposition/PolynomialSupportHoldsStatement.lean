import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_support_holds : PolSuppSt := by
  first | exact @GlobalTheory.TorRef.polSuppSt | exact GlobalTheory.TorRef.polSuppSt | (intros; apply GlobalTheory.TorRef.polSuppSt <;> assumption)
