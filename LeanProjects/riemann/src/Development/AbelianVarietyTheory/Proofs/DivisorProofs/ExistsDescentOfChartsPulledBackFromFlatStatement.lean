import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfChartsPulledBackFromFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_of_charts_pulled_back_from_flat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R) (f : X ⟶ S), IsProper π → Surjective π → IsIntegral S → ∀ (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)), Φ ≫ pullback.snd _ _ = pullback.snd _ _ → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → ∃ (G : Over (Sp R)) (β : X ⟶ G.left) (ψ : J → (U.left ⟶ G.left)), (∀ j, IsOpenImmersion (ψ j) ∧ ψ j ≫ G.hom = U.hom ∧ e j ≫ β = pullback.fst _ _ ≫ ψ j) ∧ (∀ g : G.left, ∃ j, g ∈ Set.range (ψ j)) ∧ IsPullback β f G.hom π ∧ pullback.fst f (pullback.fst π π) ≫ β = Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
  first | exact @GlobalTheory.Mum.ChartDescent.exists_descent | exact GlobalTheory.Mum.ChartDescent.exists_descent | (intros; apply GlobalTheory.Mum.ChartDescent.exists_descent <;> assumption)
