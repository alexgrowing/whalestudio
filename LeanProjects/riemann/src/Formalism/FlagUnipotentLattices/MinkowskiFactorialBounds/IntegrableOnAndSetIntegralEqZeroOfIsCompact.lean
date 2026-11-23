import Formalism.FlagUnipotentLattices.BlockDistFromLows
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.InterlacingOfBlocksSecondCase

open Formalism.HermitianLatticeCounting.S8 Finset MeasureTheory Filter Topology TensorProduct

set_option linter.all false

noncomputable section

namespace Formalism.HermitianLatticeCounting.P

example (f : Fin 2 → ℝ) (g : ℝ) : (∑ i, f i + g) = (∑ i, f i) + g := rfl

theorem explicit_constant_bound : ExplicitC := by
  intro n q h hn hq0 hq
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set s := Real.sqrt q with hs
  set σ := Real.sqrt (n : ℝ) with hσ
  have s0 : 0 ≤ s := Real.sqrt_nonneg _
  have σ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have s2 : s ^ 2 = q := Real.sq_sqrt hq0
  have σ2 : σ ^ 2 = n := Real.sq_sqrt (by linarith)
  have σ1 : 1 ≤ σ := by
    rw [hσ]; exact Real.one_le_sqrt.2 (by linarith)
  have σn : σ ≤ n := by nlinarith
  have hsσ : s ≤ 5 / 7 * σ := by
    by_contra hc
    push Not at hc
    have := pow_lt_pow_left₀ hc (by positivity) (two_ne_zero)
    nlinarith
  have hdiv : (((n ^ 2 / 2 + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ 2 / 2 + 1 := by
    push_cast
    have := Nat.cast_div_le (α := ℝ) (m := n ^ 2) (n := 2)
    push_cast at this
    linarith
  have n2 : 0 ≤ (n : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hdiv s0]
  · nlinarith [mul_le_mul_of_nonneg_left σn n2]
  · intro hh
    have A : (n : ℝ) ^ 2 * s ≤ 5 / 7 * ((n : ℝ) ^ 2 * σ) := by nlinarith [mul_le_mul_of_nonneg_left hsσ n2]
    have B : 0 ≤ (n : ℝ) ^ 2 * σ := by positivity
    have C : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * σ := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · have : (n : ℝ) * (q * s) ≤ (n : ℝ) ^ 2 / 2 * s := by
        have : (n : ℝ) * q ≤ (n : ℝ) ^ 2 / 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this s0]
      nlinarith
    · have h2 : (2 : ℝ) * s ≤ (n : ℝ) ^ 2 / 2 * s := by nlinarith [mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 by nlinarith) s0]
      have h3 : ((n : ℝ) - 1) * q ≤ (n : ℝ) ^ 2 / 2 := by nlinarith
      nlinarith
    · nlinarith

def continuousTestFunctions {X : Type} [TopologicalSpace X] (𝒜 : Set (X → ℂ)) : Set C(X, ℂ) := {a | (a : X → ℂ) ∈ 𝒜}

end Formalism.HermitianLatticeCounting.P
