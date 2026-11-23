import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficient
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_constant_fourier_coefficient : MapsExist → PositivityTheory.PfSWUS.FourierZero → PcFc := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.target | exact GlobalTheory.CompanionTheory.PcFc.target | (intros; apply GlobalTheory.CompanionTheory.PcFc.target <;> assumption)
