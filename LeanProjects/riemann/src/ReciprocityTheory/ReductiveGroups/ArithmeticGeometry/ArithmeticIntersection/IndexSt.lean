import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AI

def IndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : Subring K),
    Module.Free ℤ O → Module.Finite ℤ O → Module.finrank ℤ O = Module.finrank ℚ K →
    ∀ f : O, f ≠ 0 →
      (Nat.card (O ⧸ Ideal.span {f}) : ℝ) = |(Algebra.norm ℚ (f : K) : ℝ)| ∧
      Real.log (Nat.card (O ⧸ Ideal.span {f})) = ∑ σ : K →+* ℂ, Real.log ‖σ f‖

end ReciprocityTheory.ChartRestriction.G.AI
