import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalizationPreservesClosedness
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_preserves_closedness : ∀ {S : Type} [CommRing S] (ϖ : S), (Val ϖ → Loc S ∧ Loc (Localization.Away ϖ)) ∧ (Aic S → Aic (Localization.Away ϖ)) := by
  first | exact @GlobalTheory.CompanionTheory.LocAic.main | exact GlobalTheory.CompanionTheory.LocAic.main | (intros; apply GlobalTheory.CompanionTheory.LocAic.main <;> assumption)
