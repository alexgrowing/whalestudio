import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationDividedPowerStructures
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_divided_power_structures : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.PdI (A.Fil0 1) ∧ R.PdI A.PFil0 ∧ ∀ x ∈ A.Fil0 1, ∀ (k : ℕ) (y : A.Acr0), (k.factorial : A.Acr0) * y = x ^ k → y ∈ A.Fil0 k := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.pdI_main | exact GlobalTheory.CompanionTheory.PerfFil.pdI_main | (intros; apply GlobalTheory.CompanionTheory.PerfFil.pdI_main <;> assumption)
