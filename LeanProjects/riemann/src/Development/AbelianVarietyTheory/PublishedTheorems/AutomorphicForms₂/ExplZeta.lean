import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def ExplZeta : Prop :=
  ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    ‖psiChi (1 : DirichletCharacter ℂ 1) x - (x : ℂ) + zsum (1 : DirichletCharacter ℂ 1) 0 T (fun ρ => (x : ℂ) ^ ρ / ρ) +
        ((Real.log (2 * Real.pi) + Real.log (1 - 1 / x ^ 2) / 2 : ℝ) : ℂ)‖ ≤
      C * (Real.log x + x / T * Real.log (x * T) ^ 2)

end GlobalTheory.Mem.An
