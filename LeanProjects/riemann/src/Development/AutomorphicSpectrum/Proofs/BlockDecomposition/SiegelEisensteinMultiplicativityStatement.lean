import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_eisenstein_multiplicativity : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Dict → PositivityTheory.RgEis.DictInf → PositivityTheory.RgEis.CMGood → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.SgAll → SiegelEisensteinSeries.BRoad.SiegelMult := by
  first | exact @GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of | exact GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of | (intros; apply GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of <;> assumption)
