import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MackeyFormulaAll
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mackey_formula_all : ReciprocityTheory.Ty.Fin.St.MackeyAll := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.mackeyAll | exact GlobalTheory.CompanionTheory.TyFin.mackeyAll | (intros; apply GlobalTheory.CompanionTheory.TyFin.mackeyAll <;> assumption)
