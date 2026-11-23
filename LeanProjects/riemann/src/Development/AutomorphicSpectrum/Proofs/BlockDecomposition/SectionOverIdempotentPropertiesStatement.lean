import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOverIdempotentProperties
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_over_idempotent_properties : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), SecOn f 0 ∧ (∀ e e' : S, SecOn f e → SecOn f (e * e')) ∧ (SecOn f 1 → ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _) := by
  first | exact @GlobalTheory.CompanionTheory.SecRules.main | exact GlobalTheory.CompanionTheory.SecRules.main | (intros; apply GlobalTheory.CompanionTheory.SecRules.main <;> assumption)
