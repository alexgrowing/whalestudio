import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosed
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieck_existence_closed : GEClosed := by
  first | exact @GlobalTheory.CompanionTheory.GE.geClosed | exact GlobalTheory.CompanionTheory.GE.geClosed | (intros; apply GlobalTheory.CompanionTheory.GE.geClosed <;> assumption)
