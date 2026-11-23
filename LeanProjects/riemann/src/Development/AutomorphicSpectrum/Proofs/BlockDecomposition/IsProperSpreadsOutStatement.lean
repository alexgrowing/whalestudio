import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOut
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_spreads_out : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) := by
  first | exact @GlobalTheory.CompanionTheory.SpreadingModels.properSpreads | exact GlobalTheory.CompanionTheory.SpreadingModels.properSpreads | (intros; apply GlobalTheory.CompanionTheory.SpreadingModels.properSpreads <;> assumption)
