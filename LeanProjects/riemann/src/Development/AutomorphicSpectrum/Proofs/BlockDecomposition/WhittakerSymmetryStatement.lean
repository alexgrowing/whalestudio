import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSymmetry
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_symmetry : ReciprocityTheory.Ty.Fin.St.WhSym := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.WhSymProof.whSym | exact GlobalTheory.CompanionTheory.TyFin.WhSymProof.whSym | (intros; apply GlobalTheory.CompanionTheory.TyFin.WhSymProof.whSym <;> assumption)
