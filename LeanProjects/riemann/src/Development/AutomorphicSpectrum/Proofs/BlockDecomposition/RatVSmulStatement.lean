import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVSmul
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lines_decomposition : Lines := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLines.lines | exact GlobalTheory.CompanionTheory.RgEisLines.lines | (intros; apply GlobalTheory.CompanionTheory.RgEisLines.lines <;> assumption)
