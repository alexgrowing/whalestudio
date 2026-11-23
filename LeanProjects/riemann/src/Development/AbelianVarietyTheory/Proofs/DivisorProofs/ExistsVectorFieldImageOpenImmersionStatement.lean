import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldImageOpenImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vectorField_image_openImmersion : ∀ (Z Z' : Scheme.{0}) (φ : Z' ⟶ Z) [IsOpenImmersion φ] (W₀ : Z'.Opens) (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)), IsField W₀ d → ∃ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField (φ ''ᵁ W₀) d₂ ∧ ∀ (O : Z.Opens), O ≤ φ ''ᵁ W₀ → ∀ f : Γ(Z, O), (φ.app O).hom (d₂ O f) = d (φ ⁻¹ᵁ O) ((φ.app O).hom f) := by
  first | exact @GlobalTheory.LogKS.isField_image | exact GlobalTheory.LogKS.isField_image | (intros; apply GlobalTheory.LogKS.isField_image <;> assumption)
