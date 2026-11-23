import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicComplete
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untilt_adic_complete : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsAdicComplete (Ideal.span {(l : A.U)}) A.U := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U | exact GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U | (intros; apply GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U <;> assumption)
