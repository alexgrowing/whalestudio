import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationDichotomy
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_localization_dichotomy : ∀ {S : Type} [CommRing S] (ϖ : S) (P : Ideal S), P.IsPrime → (Val ϖ → Dich (Ideal.Quotient.mk (compI P) ϖ)) ∧ (ϖ ∈ nonZeroDivisors S → Ideal.Quotient.mk (compI P) ϖ ∈ nonZeroDivisors (S ⧸ compI P)) := by
  first | exact @GlobalTheory.CompanionTheory.CompDich.dich_comp | exact GlobalTheory.CompanionTheory.CompDich.dich_comp | (intros; apply GlobalTheory.CompanionTheory.CompDich.dich_comp <;> assumption)
