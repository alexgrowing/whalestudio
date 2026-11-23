import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm

open GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.MBLow.Cl

def cubF {B : NumB ℂ} {g : ℕ} (d : AB B g) (x y z : Fin g → ℂ) : ℂ :=
  (B.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) /
    (d.fr (x + y + z) * d.fr x * d.fr y * d.fr z)

end GlobalTheory.MBLow.Cl

end
