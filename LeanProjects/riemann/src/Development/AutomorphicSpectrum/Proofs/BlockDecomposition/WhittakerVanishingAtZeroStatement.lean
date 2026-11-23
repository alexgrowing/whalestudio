import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVanishingAtZero
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_vanishing_at_zero : Ad3.SchwartzSpaceL2.SDZ := by
  first | exact @GlobalTheory.CompanionTheory.DoubleTate.sdz | exact GlobalTheory.CompanionTheory.DoubleTate.sdz | (intros; apply GlobalTheory.CompanionTheory.DoubleTate.sdz <;> assumption)
