import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ConePolar.Statement : Prop :=
  ∀ e : ℕ, ∃ κ : ℝ, ∀ (n : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (g : (Fin n → ℂ) → ℝ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) →
    ContinuousOn g {x | x ≠ 0} →
      coneIntegral h J e g =
        κ * varInt (J ⊔ Ideal.span {linForm ℓ - 1}) e g (fun _ x => Real.log (h.dualNorm x))

theorem isProjPrime_bot_space (n : ℕ) : IsProjPrime (⊥ : Ideal (MvPolynomial (Fin (n + 1)) ℂ)) where
  isPrime := Ideal.isPrime_bot
  isHomog f hf d := by
    rw [Ideal.mem_bot] at hf ⊢
    rw [hf, map_zero]
  isRelevant := ⟨0, fun hX => X_ne_zero (0 : Fin (n + 1)) (Ideal.mem_bot.mp hX)⟩

end

end GroundTheory.Heights₂.Heights
