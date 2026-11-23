import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InductionInStagesTwoFactorsEquiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inductionInStages_twoFactors_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {β₀ β₁ a b n V W U : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (E : (Σ c, m c) ≃ n) (h : a ⊕ b ≃ n) (ψ₀ : (Σ i, m (toLex (Sum.inl i))) ≃ a) (ψ₁ : (Σ j, m (toLex (Sum.inr j))) ≃ b), (∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩) → (∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩) → ∀ (ρ₀ : Representation ℂ (Levi k fun i => m (toLex (Sum.inl i))) V) (ρ₁ : Representation ℂ (Levi k fun j => m (toLex (Sum.inr j))) W) (σ : Representation ℂ (Levi k m) U) (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U), (∀ g x, σ g (κ x) = κ (TensorProduct.map (ρ₀ fun i => g (toLex (.inl i))) (ρ₁ fun j => g (toLex (.inr j))) x)) → Nonempty ((ind₂ h (extTensor (parInd ψ₀ ρ₀) (parInd ψ₁ ρ₁))).Equiv (parInd E σ)) := by
  first | exact @GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv | exact GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv | (intros; apply GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv <;> assumption)
