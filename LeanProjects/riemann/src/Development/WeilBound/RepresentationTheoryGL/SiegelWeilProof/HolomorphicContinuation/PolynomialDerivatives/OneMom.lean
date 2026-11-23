import Mathlib

noncomputable section

namespace PositivityTheory.Rg.Sw.LC

def OneMom : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ p q : ℕ,
    MeasureTheory.Integrable (fun z : ℂ => z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))) ∧
    ∫ z : ℂ, z ^ p * star z ^ q * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) =
      if p = q then ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) else 0

end PositivityTheory.Rg.Sw.LC
