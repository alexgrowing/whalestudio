import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeafBound
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leaf_bound_alt : GlobalTheory.CompanionTheory.EGlue.DiscInf → GlobalTheory.CompanionTheory.EGlue.TopInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.LeafBound := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound | exact GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound | (intros; apply GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound <;> assumption)
