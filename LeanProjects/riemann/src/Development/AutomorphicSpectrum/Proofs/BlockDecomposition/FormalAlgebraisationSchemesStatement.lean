import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalAlgebraisationSchemes
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_algebraisation_schemes : GEClosedProj → GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj | exact GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj <;> assumption)
