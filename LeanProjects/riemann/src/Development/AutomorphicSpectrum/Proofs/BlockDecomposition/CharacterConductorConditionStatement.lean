import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_conductor_condition : PositivityTheory.SiegelWeilFormula.Gunr.PsiCond := by
  first | exact @GlobalTheory.CompanionTheory.PsiCondLoc.psiCond | exact GlobalTheory.CompanionTheory.PsiCondLoc.psiCond | (intros; apply GlobalTheory.CompanionTheory.PsiCondLoc.psiCond <;> assumption)
