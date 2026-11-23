import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pattern_group_statement : ReciprocityTheory.Ty.Fin.St.PatGroup := by
  first | exact @GlobalTheory.CompanionTheory.PatGrp.patGroup | exact GlobalTheory.CompanionTheory.PatGrp.patGroup | (intros; apply GlobalTheory.CompanionTheory.PatGrp.patGroup <;> assumption)
