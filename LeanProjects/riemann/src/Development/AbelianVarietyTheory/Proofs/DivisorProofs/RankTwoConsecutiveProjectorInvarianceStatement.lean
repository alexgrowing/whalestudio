import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoConsecutiveProjectorInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_two_consecutive_projector_invariance : GlobalTheory.LeviCut.RankTwo := by
  first | exact @GlobalTheory.LeviCut.RankTwoProof.rankTwo | exact GlobalTheory.LeviCut.RankTwoProof.rankTwo | (intros; apply GlobalTheory.LeviCut.RankTwoProof.rankTwo <;> assumption)
