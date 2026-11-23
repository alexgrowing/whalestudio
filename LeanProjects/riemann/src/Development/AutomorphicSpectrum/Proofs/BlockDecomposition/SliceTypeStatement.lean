import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceType
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_type : GlobalTheory.CompanionTheory.EGlue.SliceType := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.SliceTypePf.main | exact GlobalTheory.CompanionTheory.EGlue.SliceTypePf.main | (intros; apply GlobalTheory.CompanionTheory.EGlue.SliceTypePf.main <;> assumption)
