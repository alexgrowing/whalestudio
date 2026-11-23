import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveActionThickeningEndosCompletePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additive_action_thickeningEndos_completePoints : ∀ (R : Type) [CommRing R] (I : Ideal R) (G : Over (Sp R)) [GrpObj G] (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G), (∀ e, IsMonHom (b e)) → (∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B] (s : Sp B ⟶ Sp R), s (closedPoint B) ∈ Set.range (thick R I 0) → ∃ Φ : (Over.mk s ⟶ G) → (Over.mk s ⟶ G), (∀ x y, Φ (x * y) = Φ x * Φ y) ∧ ∀ (x : Over.mk s ⟶ G) (e : ℕ), ∃ r : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ (thickObj R I e G).left, r ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left ∧ r ≫ (b e).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ (Φ x).left := by
  first | exact @GlobalTheory.exists_mul_map_points_of_thickEndo | exact GlobalTheory.exists_mul_map_points_of_thickEndo | (intros; apply GlobalTheory.exists_mul_map_points_of_thickEndo <;> assumption)
