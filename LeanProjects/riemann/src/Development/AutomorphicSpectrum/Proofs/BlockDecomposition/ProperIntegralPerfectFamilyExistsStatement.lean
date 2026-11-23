import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperIntegralPerfectFamilyExists
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulOfAway
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_integral_perfect_family_exists : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ N : LB (A ⊗ Y).left, N.IsLB →
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (j : Spec (CommRingCat.of R) ⟶ Y.left),
    ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB ∧ Nonempty (Perf f M) ∧
      Nonempty (Perf f (pw M (-1))) ∧ IsProper f ∧ GeometricallyIntegral f ∧ Surjective f ∧
      (∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)),
        IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom) ∧
      ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
        (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
        (Triv (M.pull π) ↔ Locus N (Spec.map (CommRingCat.ofHom g) ≫ j)) := by
  first | exact @GlobalTheory.CompanionTheory.TrivLoc.exists_chart_family | exact GlobalTheory.CompanionTheory.TrivLoc.exists_chart_family | (intros; apply GlobalTheory.CompanionTheory.TrivLoc.exists_chart_family <;> assumption)
