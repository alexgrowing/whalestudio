import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialRootsOfClosedQuotient
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_roots_of_closed_quotient : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S ⧸ Ideal.span {ϖ ^ 2}) → Roots ϖ := by
  first | exact @GlobalTheory.CompanionTheory.RootsUpToUnits.roots_of_dich | exact GlobalTheory.CompanionTheory.RootsUpToUnits.roots_of_dich | (intros; apply GlobalTheory.CompanionTheory.RootsUpToUnits.roots_of_dich <;> assumption)
