import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpoly
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrreducible_constituent_ranks_unique_of_charpoly : SSRankUnique := by
  first | exact @GlobalTheory.SSRank.ssRankUnique_holds | exact GlobalTheory.SSRank.ssRankUnique_holds | (intros; apply GlobalTheory.SSRank.ssRankUnique_holds <;> assumption)
