import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.StatementD

open Matrix Finset

noncomputable section

namespace GlobalTheory.WigSh

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

def WigMap (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {V₁ V₂ : Type} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (π₂ : Q.Mx k r → (V₂ →L[ℂ] V₂)) (π₁ : Q.Mx k r → (V₁ →L[ℂ] V₁))
    (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (V₂ →L[ℂ] V₁)) : Prop :=
  (∃ (t : ℕ) (q : Fin t → MvPolynomial (Fin (2 * r + k + 1) ⊕ Fin (2 * r + k + 1)) ℂ) (Lm : Fin t → (V₂ →L[ℂ] V₁)),
      (∀ i, (q i).totalDegree ≤ d) ∧
        ∀ ω, A ω = ∑ i, MvPolynomial.eval (Sum.elim ω (fun j => star (ω j))) (q i) • Lm i) ∧
    (∀ h ∈ UWset k r z, ∀ ω, (A (h *ᵥ ω)).comp (π₂ h) = (π₁ h).comp (A ω)) ∧
    (∀ (t : ℝ) (ω : Fin (2 * r + k + 1) → ℂ), A ((t : ℂ) • ω) = ((t : ℂ) ^ d) • A ω) ∧
    ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ‖A ω‖ ^ 2 ≤ (herm (Hpk k r) ω ω).re ^ d

def omg (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) : Fin (2 * r + k + 1) → ℂ :=
  D.prW k r z' ((Hpk k r * gᴴ * Hpk k r) *ᵥ
    ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a)

end GlobalTheory.WigSh
