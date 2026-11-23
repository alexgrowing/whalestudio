import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFieldEmbeddingStalkOfFiniteStalkMap
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_fieldEmbedding_stalk_of_finite_stalkMap : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (p : Sp Ω ⟶ X), (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ φ : X.presheaf.stalk (p.base (genericPoint (Sp Ω))) →+* Ω, φ.Finite ∧ ∀ (K : Type) [Field K] (τ₁ τ₂ : Ω →+* K), spMap τ₁ ≫ p = spMap τ₂ ≫ p → τ₁.comp φ = τ₂.comp φ := by
  first | exact @GlobalTheory.StalkField.exists_stalk_field_hom | exact GlobalTheory.StalkField.exists_stalk_field_hom | (intros; apply GlobalTheory.StalkField.exists_stalk_field_hom <;> assumption)
