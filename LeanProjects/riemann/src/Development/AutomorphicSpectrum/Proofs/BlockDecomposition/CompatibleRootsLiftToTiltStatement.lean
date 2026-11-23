import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompatibleRootsLiftToTilt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_roots_lift_to_tilt : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (u : ℕ → A.U), (∀ i, u (i + 1) ^ l = u i) → ∃ a : ℕ → A.A, (∀ i, a (i + 1) ^ l = a i) ∧ ∀ i, A.sharp (a i) = u i := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.exists_compatible_roots_of_sharp | exact GlobalTheory.CompanionTheory.Untilt.exists_compatible_roots_of_sharp | (intros; apply GlobalTheory.CompanionTheory.Untilt.exists_compatible_roots_of_sharp <;> assumption)
