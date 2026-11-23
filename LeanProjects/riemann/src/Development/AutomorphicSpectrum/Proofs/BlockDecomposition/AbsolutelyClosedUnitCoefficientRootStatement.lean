import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedUnitCoefficientRoot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolutely_closed_unit_coefficient_root : ∀ {S : Type} [CommRing S] , Aic S → (∀ a b : S, IsUnit (a + b) → IsUnit a ∨ IsUnit b) → ∀ (Q : Polynomial S) (i : ℕ), Q.coeff 0 = 1 → 0 < i → IsUnit (Q.coeff i) → ∃ y, Q.eval y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.UnitRoot.exists_root | exact GlobalTheory.CompanionTheory.UnitRoot.exists_root | (intros; apply GlobalTheory.CompanionTheory.UnitRoot.exists_root <;> assumption)
