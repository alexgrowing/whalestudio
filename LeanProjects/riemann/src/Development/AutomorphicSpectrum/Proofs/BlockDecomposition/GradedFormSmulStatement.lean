import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormSmul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_smul : GlobalTheory.CompanionTheory.GrForm.StSmul := by
  first | exact @GlobalTheory.CompanionTheory.GrFormSmul.stSmul | exact GlobalTheory.CompanionTheory.GrFormSmul.stSmul | (intros; apply GlobalTheory.CompanionTheory.GrFormSmul.stSmul <;> assumption)
