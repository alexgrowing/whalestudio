import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGlue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def GlueTwo.Statement : Prop :=
  ∀ (X : Scheme.{0}) (O₁ O₂ O O₁₂ : X.Opens) (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O), O ≤ O₁ ⊔ O₂ →
    ∀ (k₁ : O₁₂ ≤ O₁) (k₂ : O₁₂ ≤ O₂), O₁ ⊓ O₂ ≤ O₁₂ →
    ∀ (F₁ : (O₁ : Scheme.{0}).Modules) (F₂ : (O₂ : Scheme.{0}).Modules)
      (ψ : (Scheme.Modules.pullback (X.homOfLE k₁)).obj F₁ ≅
        (Scheme.Modules.pullback (X.homOfLE k₂)).obj F₂),
    ∃ (F : (O : Scheme.{0}).Modules) (e₁ : (Scheme.Modules.pullback (X.homOfLE h₁)).obj F ≅ F₁)
      (e₂ : (Scheme.Modules.pullback (X.homOfLE h₂)).obj F ≅ F₂),
      pullbackCompIso (X.homOfLE_homOfLE k₂ h₂) e₂ =
        pullbackCompIso (X.homOfLE_homOfLE k₁ h₁) e₁ ≪≫ ψ

end

end GroundTheory.Heights₂.Heights.Model
