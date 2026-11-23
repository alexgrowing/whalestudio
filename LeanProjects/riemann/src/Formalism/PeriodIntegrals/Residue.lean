import Mathlib

open NumberField

noncomputable section

namespace PI

def ResidueBound : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E], 2 ≤ Module.finrank ℚ E →
    dedekindZeta_residue E ≤
      (C * Real.log (((|discr E| : ℤ) : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ E))) ^ Module.finrank ℚ E

end PI
