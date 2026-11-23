import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSectionOfHeights
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_section_of_heights : HtExist → RSec := by
  first | exact @GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist | exact GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist | (intros; apply GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist <;> assumption)
