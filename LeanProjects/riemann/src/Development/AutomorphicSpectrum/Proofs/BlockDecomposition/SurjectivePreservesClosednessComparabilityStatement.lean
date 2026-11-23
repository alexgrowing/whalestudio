import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectivePreservesClosednessComparability
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_preserves_closedness_comparability : ∀ {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T), Function.Surjective φ → (Aic S → Aic T) ∧ (Val0 S → Val0 T) := by
  first | exact @GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective | exact GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective | (intros; apply GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective <;> assumption)
