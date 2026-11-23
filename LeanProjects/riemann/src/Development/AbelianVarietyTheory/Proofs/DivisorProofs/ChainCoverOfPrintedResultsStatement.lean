import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainCoverOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransport
open GlobalTheory.ChainPts
theorem _root_.GlobalTheory.T.chain_cover_of_hypotheses : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd → GlobalTheory.GroupBplus.GroupAllSt → GlobalTheory.ChainPts.ChainCoverSt := by
  first | exact @GlobalTheory.ChainPts.Cover.chainCoverSt | exact GlobalTheory.ChainPts.Cover.chainCoverSt | (intros; apply GlobalTheory.ChainPts.Cover.chainCoverSt <;> assumption)
