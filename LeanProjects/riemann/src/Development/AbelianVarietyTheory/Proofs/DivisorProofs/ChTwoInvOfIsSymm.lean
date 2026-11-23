import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcExtensionTraceChernForms

open Matrix Filter Topology GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.HodgeChTwo

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem chTwo_changeFrame {g : ℕ} {H A : E → Matrix (Fin g) (Fin g) ℂ} {z : E} (h : MContDiffAt 2 H z)
    (hu : IsUnit (H z).det) (hA : MContDiffAt 2 A z) (hAu : IsUnit (A z).det)
    (hA0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar A x η = 0) (ξ₁ η₁ ξ₂ η₂ : E) :
    chTwo (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) z ξ₁ η₁ ξ₂ η₂ = chTwo H z ξ₁ η₁ ξ₂ η₂ := by
  simp only [GlobalTheory.SubQuotChTwo.chTwo_eq_trace, curv_changeFrame h hu hA hAu hA0]
  have hc : ∀ P Q : Matrix (Fin g) (Fin g) ℂ,
      ((A z)⁻¹ * P * A z * ((A z)⁻¹ * Q * A z)).trace = (P * Q).trace := by
    intro P Q
    rw [show (A z)⁻¹ * P * A z * ((A z)⁻¹ * Q * A z) = (A z)⁻¹ * (P * Q) * A z by
      simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hAu], Matrix.trace_mul_cycle,
      mul_nonsing_inv _ hAu, Matrix.one_mul]
  simp only [hc]

theorem chTwo_inv_of_isSymm {g : ℕ} {Y : E → Matrix (Fin g) (Fin g) ℂ} {z : E} (h : MContDiffAt 2 Y z)
    (hu : IsUnit (Y z).det) (hs : ∀ᶠ x in 𝓝 z, (Y x).IsSymm) (ξ₁ η₁ ξ₂ η₂ : E) :
    chTwo (fun x => (Y x)⁻¹) z ξ₁ η₁ ξ₂ η₂ = chTwo Y z ξ₁ η₁ ξ₂ η₂ := by
  have he : (fun x => (Y x)⁻¹) =ᶠ[𝓝 z] fun x => GlobalTheory.HermFrame.dualGram (Y x) := hs.mono fun x hx => by
    show (Y x)⁻¹ = (Y x)⁻¹ᵀ
    rw [transpose_nonsing_inv, hx.eq]
  have hc : ∀ ξ η, curv (fun x => (Y x)⁻¹) z ξ η = -(curv Y z ξ η)ᵀ := fun ξ η => by
    rw [curv_congr he, curv_dual h hu]
  have ht : ∀ P Q : Matrix (Fin g) (Fin g) ℂ, (-Pᵀ * -Qᵀ).trace = (Q * P).trace := fun P Q => by
    rw [neg_mul_neg, ← Matrix.transpose_mul, Matrix.trace_transpose]
  rw [GlobalTheory.SubQuotChTwo.chTwo_eq_trace, GlobalTheory.SubQuotChTwo.chTwo_eq_trace, hc, hc, hc, hc, ht, ht, ht, ht]
  ring

example (g : ℕ) (C : Matrix (Fin g) (Fin g) ℂ) (z ξ₁ η₁ ξ₂ η₂ : E) : chTwo (fun _ => C) z ξ₁ η₁ ξ₂ η₂ = 0 := by
  simp [chTwo, wedge]

end GlobalTheory.HodgeChTwo
