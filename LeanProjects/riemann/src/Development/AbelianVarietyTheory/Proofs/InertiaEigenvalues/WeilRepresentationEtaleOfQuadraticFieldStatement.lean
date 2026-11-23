import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationEtale_of_quadraticField : WeilField → WeilEt := by
  first | exact @GlobalTheory.JR.weilEt_of_weilField | exact GlobalTheory.JR.weilEt_of_weilField | (intros; apply GlobalTheory.JR.weilEt_of_weilField <;> assumption)
