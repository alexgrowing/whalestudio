import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormExistsOfCocycle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_exists_of_cocycle : GlobalTheory.CompanionTheory.GrForm.StCocycle → GlobalTheory.CompanionTheory.GrForm.StExists := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.exists_of_cocycle | exact GlobalTheory.CompanionTheory.GrForm.exists_of_cocycle | (intros; apply GlobalTheory.CompanionTheory.GrForm.exists_of_cocycle <;> assumption)
