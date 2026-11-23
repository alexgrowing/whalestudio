import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt

noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix

namespace GlobalTheory.Published

open GlobalTheory.SmoothGlob

def CasselmanWallachLift : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
      (p : ℕ → Seminorm ℂ E) (π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)), IsSmoothModRep ε p π dπ →
      ∀ T₀ : H →ₗ[ℂ] E, IsGKMap ε σ π dπ T₀ →
        ∃ T : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T v = T₀ v) ∧ IsSmoothGMap ε σ p π T ∧
          ∀ T' : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T' v = T₀ v) → IsSmoothGMap ε σ p π T' →
            ∀ w, SmoothVec (lieSet ε) σ w → T' w = T w

end GlobalTheory.Published

end
