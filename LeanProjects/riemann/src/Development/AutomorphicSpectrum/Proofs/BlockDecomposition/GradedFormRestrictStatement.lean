import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormRestrict
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_restrict : GlobalTheory.CompanionTheory.GrForm.StRes := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stRes | exact GlobalTheory.CompanionTheory.GrForm.stRes | (intros; apply GlobalTheory.CompanionTheory.GrForm.stRes <;> assumption)
