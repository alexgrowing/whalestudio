import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.HCFdeg

noncomputable section

namespace PI

open PI.UpqRep

def FdegScale : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (s : NNReal), 0 < s → ∀ (lam : Fin n → ℝ), IsHCParam lam →
    ∃ d0 : ℝ, 0 < d0 ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (d : ℝ),
      IsDS ε lam σ → IsFdeg ((s : ENNReal) • muG ε) σ d → d = d0

end PI
