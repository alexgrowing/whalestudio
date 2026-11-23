import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonPolygonSlopeExistence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newton_polygon_slope_existence : ∀ {S : Type} [CommRing S] (ϖ : S), Dich ϖ → Roots ϖ → ∀ (q : ℕ → S) (d M : ℕ), 0 < d → q d = 1 → q 0 ∣ ϖ ^ M → ∃ c : S, (∀ i, 1 ≤ i → i ≤ d → q 0 ∣ q i * c ^ i) ∧ ∃ i, 1 ≤ i ∧ i ≤ d ∧ q i * c ^ i ∣ q 0 := by
  first | exact @GlobalTheory.CompanionTheory.NewtonSlope.first_slope | exact GlobalTheory.CompanionTheory.NewtonSlope.first_slope | (intros; apply GlobalTheory.CompanionTheory.NewtonSlope.first_slope <;> assumption)
