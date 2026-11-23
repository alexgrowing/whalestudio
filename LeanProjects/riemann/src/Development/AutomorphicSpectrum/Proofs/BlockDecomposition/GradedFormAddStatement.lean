import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAdd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_add : GlobalTheory.CompanionTheory.GrForm.StAdd := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stAdd | exact GlobalTheory.CompanionTheory.GrForm.stAdd | (intros; apply GlobalTheory.CompanionTheory.GrForm.stAdd <;> assumption)
