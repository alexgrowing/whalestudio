import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerPureTensorFormula
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_pure_tensor_formula : Ad3.SchwartzSpaceL2.SPure := by
  first | exact @GlobalTheory.CompanionTheory.PlanePure.schwartzBruhat2_eq_sum_pt | exact GlobalTheory.CompanionTheory.PlanePure.schwartzBruhat2_eq_sum_pt | (intros; apply GlobalTheory.CompanionTheory.PlanePure.schwartzBruhat2_eq_sum_pt <;> assumption)
