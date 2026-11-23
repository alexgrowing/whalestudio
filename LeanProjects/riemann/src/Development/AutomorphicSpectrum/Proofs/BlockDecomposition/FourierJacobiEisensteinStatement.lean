import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisenstein
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_jacobi_eisenstein : ZUnfold → ThTwist → FJEis := by
  first | exact @GlobalTheory.CompanionTheory.FJE.fjEis | exact GlobalTheory.CompanionTheory.FJE.fjEis | (intros; apply GlobalTheory.CompanionTheory.FJE.fjEis <;> assumption)
