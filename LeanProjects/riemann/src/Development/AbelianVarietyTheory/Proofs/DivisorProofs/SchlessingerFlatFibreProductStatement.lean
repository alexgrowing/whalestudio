import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchlessingerFlatFibreProduct
import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schlessinger_flat_fibreProduct : ∀ (P R₁ R₂ R₀ B₁ B₂ B₀ B : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀) (a₁ : R₁ ⟶ B₁) (a₂ : R₂ ⟶ B₂) (a₀ : R₀ ⟶ B₀) (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₀) (c₁ : B ⟶ B₁) (c₂ : B ⟶ B₂) (a : P ⟶ B), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → IsPushout a₁ g₁ b₁ a₀ → IsPushout a₂ g₂ b₂ a₀ → a₁.hom.Flat → a₂.hom.Flat → IsPullback c₁ c₂ b₁ b₂ → a ≫ c₁ = f₁ ≫ a₁ → a ≫ c₂ = f₂ ≫ a₂ → a.hom.Flat ∧ IsPushout a f₁ c₁ a₁ ∧ IsPushout a f₂ c₂ a₂ := by
  first | exact @GlobalTheory.SchlessingerFlat.schlessinger_flat | exact GlobalTheory.SchlessingerFlat.schlessinger_flat | (intros; apply GlobalTheory.SchlessingerFlat.schlessinger_flat <;> assumption)
