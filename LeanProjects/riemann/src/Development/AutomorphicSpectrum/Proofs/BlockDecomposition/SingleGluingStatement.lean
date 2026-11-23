import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleGluing
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.single_gluing : GlobalTheory.CompanionTheory.EGlue.PairSlices → GlobalTheory.CompanionTheory.EGlue.PairRestrict → GlobalTheory.CompanionTheory.EGlue.PairFD → GlobalTheory.CompanionTheory.EGlue.SliceType → GlobalTheory.CompanionTheory.EGlue.PairStep₁ → GlobalTheory.CompanionTheory.EGlue.PairStep₂ → GlobalTheory.CompanionTheory.EGlue.HullGen → GlobalTheory.CompanionTheory.EGlue.CapEquiv → GlobalTheory.CompanionTheory.EGlue.OneStep := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.OneStepProof.oneStep_of_parts | exact GlobalTheory.CompanionTheory.EGlue.OneStepProof.oneStep_of_parts | (intros; apply GlobalTheory.CompanionTheory.EGlue.OneStepProof.oneStep_of_parts <;> assumption)
