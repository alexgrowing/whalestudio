import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerQuotientExists
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_quotient_exists : ∀ {S : Type} [CommRing S] , TF S → ∀ I J : Ideal S, PdI I → (∀ x ∈ I, x ∈ J → ∀ k : ℕ, k ≠ 0 → ∀ y : S, (k.factorial : S) * y = x ^ k → y ∈ J) → ∃ δ : DividedPowers (I.map (Ideal.Quotient.mk J)), IsPd (Ideal.Quotient.mk J) I δ := by
  first | exact @GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient | exact GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient | (intros; apply GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient <;> assumption)
