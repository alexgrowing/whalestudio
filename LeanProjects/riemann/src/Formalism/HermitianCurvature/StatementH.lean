import Mathlib

namespace Formalism.FourierDecayAlt.H

open Real

def HerglotzZd : Prop :=
  ∀ (d : ℕ) (A : (Fin d → ℤ) → ℂ), Summable (fun σ => ‖A σ‖) →
    (∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
        0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re) →
    ∀ x : Fin d → ℝ,
      0 ≤ (∑' σ, A σ * Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ))).re

def HerglotzFejerZd : Prop :=
  ∀ (d : ℕ) (A : (Fin d → ℤ) → ℂ),
    (∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
        0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re) →
    ∀ (N : ℕ) (x : Fin d → ℝ),
      0 ≤ (∑ σ ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N),
        (((∏ j, (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1))) : ℝ) : ℂ) * A σ *
          Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ))).re

end Formalism.FourierDecayAlt.H
