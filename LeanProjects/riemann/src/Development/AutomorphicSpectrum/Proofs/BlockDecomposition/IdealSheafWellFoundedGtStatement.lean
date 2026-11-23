import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealSheafWellFoundedGt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_sheaf_well_founded_gt : ∀ {X : Scheme.{0}} [IsNoetherian X], WellFoundedGT X.IdealSheafData := by
  first | exact @GlobalTheory.CompanionTheory.GE.idealSheafData_wellFoundedGT | exact GlobalTheory.CompanionTheory.GE.idealSheafData_wellFoundedGT | (intros; apply GlobalTheory.CompanionTheory.GE.idealSheafData_wellFoundedGT <;> assumption)
