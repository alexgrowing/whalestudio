import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridDenominatorBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projector_grid_denominator_bound : GlobalTheory.LeviCut.GridInt := by
  first | exact @GlobalTheory.LeviCut.gridInt_holds | exact GlobalTheory.LeviCut.gridInt_holds | (intros; apply GlobalTheory.LeviCut.gridInt_holds <;> assumption)
