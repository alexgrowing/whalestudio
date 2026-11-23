import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRightTranslation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_right_translation : Ad3.SchwartzSpaceL2.STrans := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerTrans.sTrans | exact GlobalTheory.CompanionTheory.WhittakerTrans.sTrans | (intros; apply GlobalTheory.CompanionTheory.WhittakerTrans.sTrans <;> assumption)
