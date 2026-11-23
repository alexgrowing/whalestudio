import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def ExplChi : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive → ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    ‖psiChi χ x + zsum χ 0 T (fun ρ => (x : ℂ) ^ ρ / ρ) + ((Real.log (x - 1) / 2 : ℝ) : ℂ) +
        χ (-1) / 2 * ((Real.log (x + 1) : ℝ) : ℂ) -
        (deriv (DirichletCharacter.LFunction χ⁻¹) 1 / DirichletCharacter.LFunction χ⁻¹ 1 +
          ((Real.log (q / (2 * Real.pi)) - Real.eulerMascheroniConstant : ℝ) : ℂ))‖ ≤
      C * (Real.log x + x / T * Real.log (q * x * T) ^ 2)

end GlobalTheory.Mem.An
