import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackAppOfIsBasisOpens
import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_app_of_isBasis_opens : ∀ (Y₀ Y₁ Y₂ Y : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (𝒱 : Set Y.Opens), TopologicalSpace.Opens.IsBasis 𝒱 → (∀ V ∈ 𝒱, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  first | exact @GlobalTheory.PinchBasis.isPullback_app_of_isBasis | exact GlobalTheory.PinchBasis.isPullback_app_of_isBasis | (intros; apply GlobalTheory.PinchBasis.isPullback_app_of_isBasis <;> assumption)
