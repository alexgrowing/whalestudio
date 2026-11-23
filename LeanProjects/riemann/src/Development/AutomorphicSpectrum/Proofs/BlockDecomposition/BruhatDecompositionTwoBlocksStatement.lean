import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionTwoBlocks
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bruhat_decomposition_two_blocks : ReciprocityTheory.Ty.Fin.St.BruhatTwo := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Bruhat.bruhatTwo | exact GlobalTheory.CompanionTheory.TyFin.Bruhat.bruhatTwo | (intros; apply GlobalTheory.CompanionTheory.TyFin.Bruhat.bruhatTwo <;> assumption)
