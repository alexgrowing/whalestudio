import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentity
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_measure_identity : MapsExist → HtExist → HeckeEta → FJEis → PcBound → RSec → EisHol → ThTotal → PcFc → SphBound → PositivityTheory.PfSWUS.FourierZero → PositivityTheory.PfSWUS.CoefDataExists → ResMu := by
  first | exact @GlobalTheory.CompanionTheory.ResMu.resMu_main | exact GlobalTheory.CompanionTheory.ResMu.resMu_main | (intros; apply GlobalTheory.CompanionTheory.ResMu.resMu_main <;> assumption)
