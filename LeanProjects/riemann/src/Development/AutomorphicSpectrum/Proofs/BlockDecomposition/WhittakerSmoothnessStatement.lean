import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_smoothness : Ad3.SchwartzSpaceL2.SSmooth := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth | exact GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth | (intros; apply GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth <;> assumption)
