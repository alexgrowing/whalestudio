import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAction
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_action : GlobalTheory.CompanionTheory.GrForm.StAct := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stAct | exact GlobalTheory.CompanionTheory.GrForm.stAct | (intros; apply GlobalTheory.CompanionTheory.GrForm.stAct <;> assumption)
