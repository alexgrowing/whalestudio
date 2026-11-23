import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationQuadraticFieldExists
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_quadraticField_exists : WeilField := by
  first | exact @GlobalTheory.JR.WeilQuad.weilField_main | exact GlobalTheory.JR.WeilQuad.weilField_main | (intros; apply GlobalTheory.JR.WeilQuad.weilField_main <;> assumption)
