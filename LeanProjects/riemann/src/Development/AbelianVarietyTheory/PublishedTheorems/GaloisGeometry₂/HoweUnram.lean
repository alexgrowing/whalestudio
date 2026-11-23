import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

noncomputable section

namespace GlobalTheory.Hk3

def HoweUnram : Prop :=
  ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M),
    LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → LocVac ρ s → Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ →
      (∀ w : M, (∀ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L),
          (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (g, 1) w = w) →
        w ∈ Submodule.span ℂ (Set.range fun h => ω (1, h) s)) ∧
      ∀ w : M, (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
          (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) →
        w ∈ Submodule.span ℂ (Set.range fun g => ω (g, 1) s)

end GlobalTheory.Hk3

end
