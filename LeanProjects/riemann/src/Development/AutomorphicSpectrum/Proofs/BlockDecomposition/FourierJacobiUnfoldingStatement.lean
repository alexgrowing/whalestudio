import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiUnfolding
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_jacobi_unfolding : ZUnfold := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.zUnfold | exact GlobalTheory.CompanionTheory.ZUnf.zUnfold | (intros; apply GlobalTheory.CompanionTheory.ZUnf.zUnfold <;> assumption)
