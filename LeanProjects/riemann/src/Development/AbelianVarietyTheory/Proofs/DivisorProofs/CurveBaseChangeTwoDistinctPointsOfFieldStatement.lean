import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveBaseChangeTwoDistinctPointsOfField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_baseChange_two_distinct_points_of_field : ∀ (R F : Type) [CommRing R] [Field F] (ψ : R →+* F) (X : Over (Sp R)) (P₁ : Polynomial R) (u₁ : Sp (Localization.Away P₁) ⟶ X.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ X.hom = spMap (algebraMap R (Localization.Away P₁)) → IsUnit (ψ P₁.leadingCoeff) → spMap ψ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap ψ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ → ∃ (P' : Polynomial F) (_ : P' ≠ 0) (u' : Sp (Localization.Away P') ⟶ ((Over.pullback (spMap ψ)).obj X).left) (a' b' : Localization.Away P' →ₐ[F] F), u' ≫ ((Over.pullback (spMap ψ)).obj X).hom = spMap (algebraMap F (Localization.Away P')) ∧ spMap a'.toRingHom ≫ u' ≠ spMap b'.toRingHom ≫ u' := by
  first | exact @GlobalTheory.curve_baseChange_two_points | exact GlobalTheory.curve_baseChange_two_points | (intros; apply GlobalTheory.curve_baseChange_two_points <;> assumption)
