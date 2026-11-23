import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainPointsOmegaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
open GlobalTheory GlobalTheory.ChainPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_points_omega_stable : GlobalTheory.ChainPts.ReadsOmSt := by
  first | exact @GlobalTheory.ChainPts.readsOmSt | exact GlobalTheory.ChainPts.readsOmSt | (intros; apply GlobalTheory.ChainPts.readsOmSt <;> assumption)
