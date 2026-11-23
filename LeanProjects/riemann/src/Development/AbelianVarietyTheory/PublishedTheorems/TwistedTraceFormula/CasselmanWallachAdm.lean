import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt

noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix

namespace GlobalTheory.Published

open GlobalTheory.SmoothGlob

def CasselmanWallachAdm : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
      (p : ℕ → Seminorm ℂ E) (π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)), IsSmoothModRep ε p π dπ →
      ∀ T₀ : H →ₗ[ℂ] E, IsGKMap ε σ π dπ T₀ →
        (∀ x : E, FiniteDimensional ℂ (Submodule.span ℂ {y : E | ∃ k ∈ Kset ε, y = π k x}) →
          ∃ v, IsKFin ε σ v ∧ T₀ v = x) →
        ∃ T : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T v = T₀ v) ∧ IsSmoothGMap ε σ p π T ∧
          IsClosed (T '' {w | SmoothVec (lieSet ε) σ w}) ∧
          ((∀ v, IsKFin ε σ v → T₀ v = 0 → v = 0) →
            ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) →
              ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → sobNorm σ S w ≤ q (T w))

end GlobalTheory.Published

end
