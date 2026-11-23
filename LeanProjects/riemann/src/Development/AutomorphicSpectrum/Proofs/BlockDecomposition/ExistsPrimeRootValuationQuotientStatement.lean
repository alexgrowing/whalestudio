import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimeRootValuationQuotient
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_root_valuation_quotient : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest → ∃ ϖ : A.U, ϖ ^ l = (l : A.U) ∧ R.Val0 (A.U ⧸ Ideal.span {ϖ ^ 2}) ∧ R.Aic (A.U ⧸ Ideal.span {ϖ ^ 2}) := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.untilt_mod_varpi_sq | exact GlobalTheory.CompanionTheory.Untilt.untilt_mod_varpi_sq | (intros; apply GlobalTheory.CompanionTheory.Untilt.untilt_mod_varpi_sq <;> assumption)
