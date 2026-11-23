import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationOfLocalDichotomy
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_of_local_dichotomy : ∀ {S : Type} [CommRing S] (ϖ : S), (∀ m : Ideal S, m.IsMaximal → Dich (Ideal.Quotient.mk (compI m) ϖ)) → Val ϖ := by
  first | exact @GlobalTheory.CompanionTheory.Idem.val_of_dich | exact GlobalTheory.CompanionTheory.Idem.val_of_dich | (intros; apply GlobalTheory.CompanionTheory.Idem.val_of_dich <;> assumption)
