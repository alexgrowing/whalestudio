import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingComparisonOfBase
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_ring_comparison_of_base : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsBase l A → (Function.Bijective A.cris0 ∧ Function.Bijective A.oC) ∧ ∀ n, Function.Surjective (A.cris n) ∧ RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} := by
  first | exact @GlobalTheory.CompanionTheory.BaseAcris.main | exact GlobalTheory.CompanionTheory.BaseAcris.main | (intros; apply GlobalTheory.CompanionTheory.BaseAcris.main <;> assumption)
