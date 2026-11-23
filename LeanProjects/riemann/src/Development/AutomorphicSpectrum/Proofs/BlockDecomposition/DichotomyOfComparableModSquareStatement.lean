import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DichotomyOfComparableModSquare
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dichotomy_of_comparable_mod_square : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := by
  first | exact @GlobalTheory.CompanionTheory.DichMod.dich_of_mod | exact GlobalTheory.CompanionTheory.DichMod.dich_of_mod | (intros; apply GlobalTheory.CompanionTheory.DichMod.dich_of_mod <;> assumption)
