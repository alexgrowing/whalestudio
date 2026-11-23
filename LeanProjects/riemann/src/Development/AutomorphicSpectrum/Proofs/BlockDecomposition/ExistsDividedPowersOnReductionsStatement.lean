import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDividedPowersOnReductions
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divided_powers_on_reductions : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ δ : DividedPowers (A.Fil n 1), R.IsPd (A.mkAcr n) (A.Fil0 1) δ) ∧ ∃ δ : DividedPowers (A.PFil n), R.IsPd (A.mkAcr n) A.PFil0 δ := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.exists_dividedPowers_fil_pfil | exact GlobalTheory.CompanionTheory.PerfFil.exists_dividedPowers_fil_pfil | (intros; apply GlobalTheory.CompanionTheory.PerfFil.exists_dividedPowers_fil_pfil <;> assumption)
