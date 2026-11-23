import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfimumOfEquality
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infimum_of_equality : GlobalTheory.CompanionTheory.EGlue.InfOfEq := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.infOfEq_holds | exact GlobalTheory.CompanionTheory.EGlue.infOfEq_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.infOfEq_holds <;> assumption)
