import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGlueTwo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def IsoGlueTwo.Statement : Prop :=
  ∀ (Y : Scheme.{0}) (P₁ P₂ P P₁₂ : Y.Opens) (h₁ : P₁ ≤ P) (h₂ : P₂ ≤ P), P ≤ P₁ ⊔ P₂ →
    ∀ (k₁ : P₁₂ ≤ P₁) (k₂ : P₁₂ ≤ P₂), P₁ ⊓ P₂ ≤ P₁₂ →
    ∀ (A B : (P : Scheme.{0}).Modules)
      (φ₁ : (Scheme.Modules.pullback (Y.homOfLE h₁)).obj A ≅ (Scheme.Modules.pullback (Y.homOfLE h₁)).obj B)
      (φ₂ : (Scheme.Modules.pullback (Y.homOfLE h₂)).obj A ≅ (Scheme.Modules.pullback (Y.homOfLE h₂)).obj B),
    pullbackIsoAlong (Y.homOfLE_homOfLE k₁ h₁) φ₁ = pullbackIsoAlong (Y.homOfLE_homOfLE k₂ h₂) φ₂ →
    ∃ φ : A ≅ B, (Scheme.Modules.pullback (Y.homOfLE h₁)).mapIso φ = φ₁ ∧
      (Scheme.Modules.pullback (Y.homOfLE h₂)).mapIso φ = φ₂

end

end GroundTheory.Heights₂.Heights.Model
