import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsomorphismProperties
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_isomorphism_properties : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts | exact GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts | (intros; apply GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts <;> assumption)
