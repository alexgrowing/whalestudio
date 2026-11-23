import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SamePartitionStatement
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_partition_statement : ReciprocityTheory.Ty.Fin.St.SamePart := by
  first | exact @GlobalTheory.CompanionTheory.TyFinSamePart.samePart | exact GlobalTheory.CompanionTheory.TyFinSamePart.samePart | (intros; apply GlobalTheory.CompanionTheory.TyFinSamePart.samePart <;> assumption)
