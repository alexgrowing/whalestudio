import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionPointsCorrespondMatchedPullbacks
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisionPoints_correspond_matched_pullbacks : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (D₀ : DegPre R) (D₁ D₂ : DegPre V), D₀.TauBimult → D₂.TauBimult → ∀ (f₁ f₂ : R →+* V) (hD₁ : IsPullDeg f₁ D₀ D₁) (hD₂ : IsPullDeg f₂ D₀ D₂) (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j₁ j₂ : F₀ →+* F) (b : D₁.P.A ⟶ D₂.P.A) (φ' : D₁.X ≃+ D₂.X) (k : ℕ), 1 ≤ k → (∀ p₀ : QkPt D₀ F₀ k, ∃ (p₁ : QkPt D₁ F k) (p₂ : QkPt D₂ F k), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → (∀ y : D₀.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y) → ∀ (y : D₀.X) (x : TF (R := R) F₀ ⟶ D₀.P.A), x ^ k = DegPre.cF D₀ F₀ y → ∃ z : TF (R := V) F ⟶ D₁.P.A, z.left ≫ hD₁.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₁) = spMap j₁ ≫ x.left ∧ z.left ≫ b.left ≫ hD₂.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₂) = spMap j₂ ≫ x.left := by
  first | exact @GlobalTheory.TInj.divPt_match_of_pairs | exact GlobalTheory.TInj.divPt_match_of_pairs | (intros; apply GlobalTheory.TInj.divPt_match_of_pairs <;> assumption)
