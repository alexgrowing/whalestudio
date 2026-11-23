import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceInfimum
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_infimum : GlobalTheory.CompanionTheory.EGlue.DiscInf → GlobalTheory.CompanionTheory.EGlue.TopInf → GlobalTheory.CompanionTheory.EGlue.ConvInf := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf | exact GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf | (intros; apply GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf <;> assumption)
