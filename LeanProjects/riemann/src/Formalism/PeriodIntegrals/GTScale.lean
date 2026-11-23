import Mathlib
import Formalism.PeriodIntegrals.GTDefs

noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def GTScale : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ),
    IsIota h lam sg io → IsBr h lam sg br → ∀ a : ℂˣ,
    (∀ s ∈ nablaSq ℂ n sg,
      (normFock lam (sqAct ℂ N lam (lastGL ℂ N a⁻¹) (io s)) (sqAct ℂ N lam (lastGL ℂ N a⁻¹) (io s))).re ≤
        ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) * brBd h lam sg ^ 2 * (normFock sg s s).re) ∧
    (∀ f ∈ delSq ℂ N lam,
      (normFock sg (br f) (br f)).re ≤ ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) * brBd h lam sg ^ 2 *
        (normFock lam (sqAct ℂ N lam (lastGL ℂ N a) f) (sqAct ℂ N lam (lastGL ℂ N a) f)).re)

end PI
