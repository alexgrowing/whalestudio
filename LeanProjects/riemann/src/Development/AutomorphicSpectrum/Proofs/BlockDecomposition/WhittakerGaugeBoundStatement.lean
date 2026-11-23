import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGaugeBound
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_gauge_bound : Ad3.SchwartzSpaceL2.SBound := by
  first | exact @GlobalTheory.CompanionTheory.DampedWhittakerGauge.whittaker_torus_gauge_estimate | exact GlobalTheory.CompanionTheory.DampedWhittakerGauge.whittaker_torus_gauge_estimate | (intros; apply GlobalTheory.CompanionTheory.DampedWhittakerGauge.whittaker_torus_gauge_estimate <;> assumption)
