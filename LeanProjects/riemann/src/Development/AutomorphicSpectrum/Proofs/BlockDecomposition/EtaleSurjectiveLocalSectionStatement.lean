import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleSurjectiveLocalSection
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_surjective_local_section : ∀ {S : Type} [CommRing S] , Aic S → Loc S → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), Etale f → Surjective f → ∀ m : Ideal S, m.IsMaximal → ∃ e : S, IsIdempotentElem e ∧ e ∉ m ∧ SecOn f e := by
  first | exact @GlobalTheory.CompanionTheory.EtaleSections.exists_secOn_of_etale_surjective | exact GlobalTheory.CompanionTheory.EtaleSections.exists_secOn_of_etale_surjective | (intros; apply GlobalTheory.CompanionTheory.EtaleSections.exists_secOn_of_etale_surjective <;> assumption)
