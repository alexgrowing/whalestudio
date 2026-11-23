import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTermOfIsotropic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_term_of_isotropic : OnlyIsotropic → EllTerm := by
  first | exact @GlobalTheory.CompanionTheory.EllIso.ellTerm_of_onlyIsotropic | exact GlobalTheory.CompanionTheory.EllIso.ellTerm_of_onlyIsotropic | (intros; apply GlobalTheory.CompanionTheory.EllIso.ellTerm_of_onlyIsotropic <;> assumption)
