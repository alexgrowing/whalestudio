import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionEndomorphismWeightBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_action_endomorphism_weight_bound : GlobalTheory.LeviCut.AdjBdd := by
  first | exact @GlobalTheory.LeviCut.adjBdd_holds | exact GlobalTheory.LeviCut.adjBdd_holds | (intros; apply GlobalTheory.LeviCut.adjBdd_holds <;> assumption)
