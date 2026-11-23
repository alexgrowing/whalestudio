import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorLimit
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_limit : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees → GlobalTheory.CompanionTheory.EGlue.LeafBound → GlobalTheory.CompanionTheory.EGlue.ConvInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.CapEquiv → GlobalTheory.CompanionTheory.EGlue.MCloseFacts → GlobalTheory.CompanionTheory.EGlue.FactorLim := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.FactorLimProof.factorLim_of_parts | exact GlobalTheory.CompanionTheory.EGlue.FactorLimProof.factorLim_of_parts | (intros; apply GlobalTheory.CompanionTheory.EGlue.FactorLimProof.factorLim_of_parts <;> assumption)
