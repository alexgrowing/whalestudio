import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingShortExact
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishing_short_exact : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (α : F₁ ⟶ F₂)
    (β : F₂ ⟶ F₃), (∀ T, Function.Injective (α.app T).hom) → (∀ T, Function.Exact (α.app T).hom (β.app T).hom) →
    (∀ T, Function.Surjective (β.app T).hom) → (∀ n, Subsingleton (CH.H F₂ n)) → (∀ n, Subsingleton (CH.H F₃ n)) →
    ∀ n, Subsingleton (CH.H F₁ n) := by
  first | exact @GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses | exact GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses | (intros; apply GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses <;> assumption)
