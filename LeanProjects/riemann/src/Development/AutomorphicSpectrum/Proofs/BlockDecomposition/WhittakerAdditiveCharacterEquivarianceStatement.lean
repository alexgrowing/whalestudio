import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_additive_character_equivariance : Ad3.SchwartzSpaceL2.SPsi := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerPsi.sPsi | exact GlobalTheory.CompanionTheory.WhittakerPsi.sPsi | (intros; apply GlobalTheory.CompanionTheory.WhittakerPsi.sPsi <;> assumption)
