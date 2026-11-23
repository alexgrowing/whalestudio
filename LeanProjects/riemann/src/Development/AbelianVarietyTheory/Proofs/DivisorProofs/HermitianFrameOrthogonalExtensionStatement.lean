import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFrameOrthogonalExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Formalism.BasicNotions.TH Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_frame_orthogonal_extension : ∀ {n n₁ r₁ s₁ : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ)
    (ι : Matrix (Fin n) (Fin n₁) ℂ) (C₁ : Matrix (Fin n₁) (Ix r₁ s₁) ℂ) (e f : Fin n → ℂ),
    (r₁ + 1) + (s₁ + 1) = n → IsFrame (ιᵀ * M * ι.map star) C₁ → θ₁ * C₁ = C₁ * Jm r₁ s₁ →
    θ * ι = ι * θ₁ → θ *ᵥ e = e → θ *ᵥ f = -f → e ⬝ᵥ M *ᵥ star e = 1 →
    f ⬝ᵥ M *ᵥ star f = -1 → e ⬝ᵥ M *ᵥ star f = 0 → f ⬝ᵥ M *ᵥ star e = 0 →
    (∀ u : Fin n₁ → ℂ, (ι *ᵥ u) ⬝ᵥ M *ᵥ star e = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star f = 0 ∧
      e ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 ∧ f ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0) →
    ∃ C : Matrix (Fin n) (Ix (r₁ + 1) (s₁ + 1)) ℂ, IsFrame M C ∧ θ * C = C * Jm (r₁ + 1) (s₁ + 1) ∧
      (∀ i, C i (.inl 0) = e i) ∧ (∀ i, C i (.inr 0) = f i) ∧
      ∀ a, a ≠ .inl 0 → a ≠ .inr 0 → ∃ z : Fin n₁ → ℂ, ∀ i, C i a = (ι *ᵥ z) i := by
  first | exact @GlobalTheory.FrameAssemble.assemble | exact GlobalTheory.FrameAssemble.assemble | (intros; apply GlobalTheory.FrameAssemble.assemble <;> assumption)
