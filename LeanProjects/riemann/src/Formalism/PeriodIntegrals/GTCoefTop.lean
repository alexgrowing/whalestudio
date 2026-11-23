import Mathlib
import Formalism.PeriodIntegrals.GTDefs

noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def GTCoefTop : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (hn : 0 < n) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    lam.w ⟨1, by omega⟩ + D0 h lam sg ≤ lam.w ⟨0, by omega⟩ →
    |((cBr h lam sg : ℤ) : ℝ)| ≤
      (((2 * (sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩) + (N : ℤ) : ℤ) : ℝ)) ^ ((((n : ℤ) * D1 h lam sg : ℤ) : ℝ)) ∧
    ∀ lam' : DomWeight N, (∀ i : Fin N, i.1 ≠ 0 → lam'.w i = lam.w i) →
      lam'.w ⟨1, by omega⟩ + D0 h lam' sg ≤ lam'.w ⟨0, by omega⟩ →
      cBr h lam' sg = cBr h lam sg ∧ D1 h lam' sg = D1 h lam sg

end PI
