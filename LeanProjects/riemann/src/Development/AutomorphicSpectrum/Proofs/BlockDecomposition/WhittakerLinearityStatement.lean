import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLinearity
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_linearity : Ad3.SchwartzSpaceL2.SLin := by
  first | exact @GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat | exact GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat | (intros; apply GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat <;> assumption)
