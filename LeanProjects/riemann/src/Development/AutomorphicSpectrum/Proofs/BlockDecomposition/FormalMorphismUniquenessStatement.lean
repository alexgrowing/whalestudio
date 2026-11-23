import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalMorphismUniqueness
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_morphism_uniqueness : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
  ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom →
  ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left),
    (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) →
  ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  first | exact @GlobalTheory.CompanionTheory.FormalUniq.eq_of_comp_thickenings_eq | exact GlobalTheory.CompanionTheory.FormalUniq.eq_of_comp_thickenings_eq | (intros; apply GlobalTheory.CompanionTheory.FormalUniq.eq_of_comp_thickenings_eq <;> assumption)
