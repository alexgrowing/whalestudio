import Formalism.PeriodIntegrals.UpqRep

noncomputable section

namespace PI

open PI.UpqRep

def HCFdeg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
      IsFdeg (muG ε) σ (c * fdegHC lam)

end PI
