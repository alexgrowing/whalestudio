import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowerDivisibilityRootExtraction
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_divisibility_root_extraction : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z := by
  first | exact @GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow | exact GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow | (intros; apply GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow <;> assumption)
