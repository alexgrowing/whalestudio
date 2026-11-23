import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTransfer
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_transfer : KH.PolyTf := by
  first | exact @GlobalTheory.CompanionTheory.PolyTfCon.polyTf | exact GlobalTheory.CompanionTheory.PolyTfCon.polyTf | (intros; apply GlobalTheory.CompanionTheory.PolyTfCon.polyTf <;> assumption)
