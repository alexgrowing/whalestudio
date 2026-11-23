import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerProductCuspidalIso
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_product_cuspidal_iso : ReciprocityTheory.Ty.Fin.St.IpCuspIso := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.IpIso.main | exact GlobalTheory.CompanionTheory.TyFin.IpIso.main | (intros; apply GlobalTheory.CompanionTheory.TyFin.IpIso.main <;> assumption)
