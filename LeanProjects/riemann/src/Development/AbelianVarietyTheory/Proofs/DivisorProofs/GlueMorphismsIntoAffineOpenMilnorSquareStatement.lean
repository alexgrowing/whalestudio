import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMorphismsIntoAffineOpenMilnorSquare
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_morphisms_into_affineOpen_milnorSquare : ∀ (S : Scheme.{0}) [IsAffine S] (U T T₁ T₂ T₀ : Over S) (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left → ∀ (V : U.left.Opens), IsAffineOpen V → ∀ (u₁ : T₁ ⟶ U) (u₂ : T₂ ⟶ U), k₁ ≫ u₁ = k₂ ≫ u₂ → (∀ x, u₁.left x ∈ V) → (∀ x, u₂.left x ∈ V) → ∃ u : T ⟶ U, j₁ ≫ u = u₁ ∧ j₂ ≫ u = u₂ := by
  first | exact @GlobalTheory.DualOpen.glue_into_affineOpen | exact GlobalTheory.DualOpen.glue_into_affineOpen | (intros; apply GlobalTheory.DualOpen.glue_into_affineOpen <;> assumption)
