import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualNumberPointsGlue
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_number_points_glue : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  (∀ a b : Sp R ⟶ X, (∀ i, spMap (algebraMap R (Localization.Away (f i))) ≫ a = spMap (algebraMap R (Localization.Away (f i))) ≫ b) → a = b) ∧
  (∀ a b : Sp (DualNumber R) ⟶ X,
    (∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ a = spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ b) → a = b) ∧
  ∀ w : ∀ i, Sp (DualNumber (Localization.Away (f i))) ⟶ X,
    (∀ i j (a : Localization.Away (f i) →+* Localization.Away (f i * f j)) (b : Localization.Away (f j) →+* Localization.Away (f i * f j)),
      a.comp (algebraMap R _) = algebraMap R _ → b.comp (algebraMap R _) = algebraMap R _ →
      spMap (dualMap a) ≫ w i = spMap (dualMap b) ≫ w j) →
    ∃ v : Sp (DualNumber R) ⟶ X, ∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ v = w i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieFinGlue.dual_glue | exact GlobalTheory.CompanionTheory.Ar.LieFinGlue.dual_glue | (intros; apply GlobalTheory.CompanionTheory.Ar.LieFinGlue.dual_glue <;> assumption)
