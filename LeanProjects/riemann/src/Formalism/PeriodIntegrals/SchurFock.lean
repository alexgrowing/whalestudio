import Mathlib
import Formalism.LocalRingCardinality.DataCoeff

noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def SchurFock : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), ∀ s ∈ nablaSq ℂ N lam,
    (∀ x ∈ Matrix.unitaryGroup (Fin N) ℂ, ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) s‖ ≤ 1) →
    (normFock lam s s).re ≤ (Module.finrank ℂ (delSq ℂ N lam) : ℝ)

end PI
