import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MackeyInnerProduct
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mackey_inner_product : ReciprocityTheory.Ty.Fin.St.MackeyIp := by
  first | exact @GlobalTheory.CompanionTheory.MackeyFn.mackeyIp | exact GlobalTheory.CompanionTheory.MackeyFn.mackeyIp | (intros; apply GlobalTheory.CompanionTheory.MackeyFn.mackeyIp <;> assumption)
