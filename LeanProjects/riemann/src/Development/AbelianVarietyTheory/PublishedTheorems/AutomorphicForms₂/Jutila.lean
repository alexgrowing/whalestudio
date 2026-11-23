import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def Jutila : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ α Q T : ℝ, 4 / 5 ≤ α → α ≤ 1 → 1 ≤ Q → 1 ≤ T →
    (({p : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ | 1 ≤ p.1.1 ∧ ((p.1.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.1.2.IsPrimitive ∧
        α ≤ p.2.re ∧ |p.2.im| ≤ T ∧ DirichletCharacter.LFunction p.1.2 p.2 = 0}.encard : ℕ∞) : ENNReal) ≤
      ENNReal.ofReal (c * (Q ^ 2 * T) ^ ((2 + ε) * (1 - α)))

end GlobalTheory.Mem.An
