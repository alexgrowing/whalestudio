import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairEmbedding
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_embedding : GlobalTheory.CompanionTheory.EGlue.PairSlices → GlobalTheory.CompanionTheory.EGlue.PairStep₁ → GlobalTheory.CompanionTheory.EGlue.PairStep₂ → GlobalTheory.CompanionTheory.EGlue.PairEmb := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairEmb_of_steps | exact GlobalTheory.CompanionTheory.EGlue.pairEmb_of_steps | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairEmb_of_steps <;> assumption)
