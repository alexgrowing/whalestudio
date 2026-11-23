import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaValueAtOne
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_value_at_one : EpMain → ZetaOne := by
  first | exact @GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain | exact GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain | (intros; apply GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain <;> assumption)
