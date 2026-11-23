import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LbSpreads
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_spreads_out' : GlobalTheory.SpreadingModels.LBSpreads := by
  first | exact @GlobalTheory.CompanionTheory.LBLimit.lbSpreads | exact GlobalTheory.CompanionTheory.LBLimit.lbSpreads | (intros; apply GlobalTheory.CompanionTheory.LBLimit.lbSpreads <;> assumption)
