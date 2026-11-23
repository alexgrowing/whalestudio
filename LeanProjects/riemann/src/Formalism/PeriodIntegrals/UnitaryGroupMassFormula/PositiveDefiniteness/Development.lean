import Mathlib
import Formalism.PeriodIntegrals.FinOrdAd

noncomputable section

namespace PI.DefPosDefWork

open Matrix ComplexOrder

def Step1 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), 0 < k → IsHerm (σ : E →+* E) J → IsDef σ J →
    ∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x)

def Step2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), 0 < k → IsHerm (σ : E →+* E) J → IsDef σ J →
    (∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x)) →
    ∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef

theorem defPosDef_of (h1 : Step1) (h2 : Step2) : PI.DefPosDef := by
  intro F E _ _ _ _ _ hF σ k J hk hH hD
  have c1 := h1 F E hF σ k J hk hH hD
  exact ⟨c1, h2 F E hF σ k J hk hH hD c1⟩

end PI.DefPosDefWork
