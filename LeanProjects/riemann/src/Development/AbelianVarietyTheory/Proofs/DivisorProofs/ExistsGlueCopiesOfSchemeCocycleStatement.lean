import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueCopiesOfSchemeCocycle
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_copies_of_scheme_cocycle : ∀ (Y : Scheme.{0}) (J : Type) (V : J → J → Y.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ Y), (∀ i, V i i = ⊤) → (∀ i, τ i i = (V i i).ι) → (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) → (∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k) → ∃ (G : Scheme.{0}) (ψ : J → (Y ⟶ G)), (∀ j, IsOpenImmersion (ψ j)) ∧ (∀ g : G, ∃ j, g ∈ Set.range (ψ j)) ∧ (∀ i j, IsPullback (V i j).ι (τ i j) (ψ i) (ψ j)) ∧ ∀ (Z : Scheme.{0}) (g : J → (Y ⟶ Z)), (∀ i j, (V i j).ι ≫ g i = τ i j ≫ g j) → ∃ F : G ⟶ Z, ∀ j, ψ j ≫ F = g j := by
  first | exact @GlobalTheory.GlueCopies.exists_glue_copies | exact GlobalTheory.GlueCopies.exists_glue_copies | (intros; apply GlobalTheory.GlueCopies.exists_glue_copies <;> assumption)
