import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOfIsUnitSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_of_isUnit_sharp' : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : A.A), IsUnit (A.sharp a) → IsUnit a := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.isUnit_of_isUnit_sharp | exact GlobalTheory.CompanionTheory.Untilt.isUnit_of_isUnit_sharp | (intros; apply GlobalTheory.CompanionTheory.Untilt.isUnit_of_isUnit_sharp <;> assumption)
