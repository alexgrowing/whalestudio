import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentInvariantOfChartwiseProjection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentInvariant_of_chartwise_projection : ∀ (B S X G : Scheme.{0}) (π : S ⟶ B) (f : X ⟶ S) (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)) (ψ : J → (U.left ⟶ G)) (β : X ⟶ G), (∀ j, IsOpenImmersion (e j)) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → (∀ j, e j ≫ β = pullback.fst _ _ ≫ ψ j) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → pullback.fst f (pullback.fst π π) ≫ β = Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
  first | exact @GlobalTheory.Mum.descent_eqn_of_chart_projection | exact GlobalTheory.Mum.descent_eqn_of_chart_projection | (intros; apply GlobalTheory.Mum.descent_eqn_of_chart_projection <;> assumption)
