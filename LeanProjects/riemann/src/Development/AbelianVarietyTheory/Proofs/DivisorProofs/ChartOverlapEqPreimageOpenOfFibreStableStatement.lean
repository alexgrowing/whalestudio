import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartOverlapEqPreimageOpenOfFibreStable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartOverlap_eq_preimage_open_of_fibre_stable : ∀ (B S X : Scheme.{0}) (π : S ⟶ B) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), IsProper π → Surjective π → (∀ j, IsOpenImmersion (e j)) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) → ∀ i j : J, ∃ V : U.left.Opens, ∀ a : ↥(pullback U.hom π), pullback.fst U.hom π a ∈ V ↔ e i a ∈ Set.range (e j) := by
  first | exact @GlobalTheory.Div.DescendOpens.overlap_preimage_open | exact GlobalTheory.Div.DescendOpens.overlap_preimage_open | (intros; apply GlobalTheory.Div.DescendOpens.overlap_preimage_open <;> assumption)
