import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_well_defined : Ad3.SchwartzSpaceL2.SWd := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerTorus.swd | exact GlobalTheory.CompanionTheory.WhittakerTorus.swd | (intros; apply GlobalTheory.CompanionTheory.WhittakerTorus.swd <;> assumption)
