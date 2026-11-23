import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvectorFixedByCompactCommuting
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IncMatTransposeConjTranspose
open scoped TensorProduct Matrix
open NumberField Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl GlobalTheory.FockInclK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_fixed_by_compact_commuting : ∀ (d d₁ R S : ℕ) (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (K θ : Matrix (Fin d) (Fin d) ℂ)
    (K₁ : Matrix (Fin d₁) (Fin d₁) ℂ) (ιH : Matrix (Fin d) (Fin d₁) ℂ) (Cw : Matrix (Fin d) (Ix (R + 1) (S + 1)) ℂ)
    (C₁w : Matrix (Fin d₁) (Ix R S) ℂ) (Y : Mat R S) (x : Fin d → ℂ) (c : ℂ), c ≠ 0 →
    (∀ i, x i = c * (Cw i (.inl r₀) + Cw i (.inr s₀))) → K *ᵥ x = x → Commute K θ →
    θ * Cw = Cw * Jm (R + 1) (S + 1) → (∀ i a, Cw i (skipIx r₀ s₀ a) = (ιH * C₁w) i a) → K * ιH = ιH * K₁ →
    C₁w * NormedSpace.exp Y = K₁ * C₁w → K * Cw = Cw * NormedSpace.exp (extMat r₀ s₀ Y) := by
  first | exact @GlobalTheory.FockInclK.mul_frame_eq_frame_mul_exp_extMat | exact GlobalTheory.FockInclK.mul_frame_eq_frame_mul_exp_extMat | (intros; apply GlobalTheory.FockInclK.mul_frame_eq_frame_mul_exp_extMat <;> assumption)
