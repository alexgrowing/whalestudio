import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open Formalism.MainNotions.S Matrix

namespace GlobalTheory.FormalDegree

def HarishChandra : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧
    ∀ (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
        IsDS (ε ∘ π) lam (fun g => σ (g.submatrix π.symm π.symm)) →
        IsFdeg (Formalism.REAL.muG ε) σ (c * Formalism.QuantumDeterminants.fdegHC lam)

theorem HarishChandra.chamber (h : HarishChandra) (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
        IsFdeg (Formalism.REAL.muG ε) σ (c * Formalism.QuantumDeterminants.fdegHC lam) := by
  obtain ⟨c, hc, h1⟩ := h n ε
  exact ⟨c, hc, fun lam hl H _ _ σ hσ => h1 1 lam hl H σ (by simpa [Equiv.Perm.one_def] using hσ)⟩

end GlobalTheory.FormalDegree
