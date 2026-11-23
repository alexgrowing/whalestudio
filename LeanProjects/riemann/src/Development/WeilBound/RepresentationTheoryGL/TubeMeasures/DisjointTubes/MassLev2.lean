import Mathlib

open NumberField

noncomputable section

namespace MainStatements.Tam

def massB (E : Type) [Field E] [NumberField E] (r : ℕ) : ℝ :=
  (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (r : ℝ) ^ 4 *
    (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ E * r ^ 2)

def massLev2 (E : Type) [Field E] [NumberField E] (r M : ℕ) : ℝ :=
  (M : ℝ) ^ (Module.finrank ℚ E * r ^ 2) * 15 ^ (Module.finrank ℚ E * r ^ 2) * massB E r

end MainStatements.Tam

end
