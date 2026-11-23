import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeUniquenessOfCovering
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransport
open GlobalTheory.ChainPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_uniqueness_of_covering : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.ChainPts.LatUniqueSt := by
  first | exact @GlobalTheory.ChainPts.LatUniq.latUniqueSt_of_classicalTheorems | exact GlobalTheory.ChainPts.LatUniq.latUniqueSt_of_classicalTheorems | (intros; apply GlobalTheory.ChainPts.LatUniq.latUniqueSt_of_classicalTheorems <;> assumption)
