import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFormsOfFormUniqueness
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
open CrystallineSemistableComparison CrystallineSemistableComparison.Onto
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_forms_of_form_uniqueness : CrystallineSemistableComparison.Onto.FormUniq → CrystallineSemistableComparison.Onto.AffOm := by
  first | exact @GlobalTheory.CompanionTheory.AffOmP.affOm | exact GlobalTheory.CompanionTheory.AffOmP.affOm | (intros; apply GlobalTheory.CompanionTheory.AffOmP.affOm <;> assumption)
