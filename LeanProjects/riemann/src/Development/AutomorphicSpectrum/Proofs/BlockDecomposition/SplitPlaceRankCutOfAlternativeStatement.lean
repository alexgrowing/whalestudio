import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_rank_cut_of_alternative : GlobalTheory.CompanionTheory.Jp.JpCondition → GlobalTheory.CompanionTheory.Jp.SplitPlaceRankCutEigenvalue := by
  first | exact @GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation | exact GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation | (intros; apply GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation <;> assumption)
