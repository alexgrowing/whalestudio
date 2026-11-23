import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraCharacter
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_character : ReciprocityTheory.Ty.Fin.St.HCChar := by
  first | exact @GlobalTheory.CompanionTheory.FinGLChar.hcChar | exact GlobalTheory.CompanionTheory.FinGLChar.hcChar | (intros; apply GlobalTheory.CompanionTheory.FinGLChar.hcChar <;> assumption)
