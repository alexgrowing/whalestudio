import Formalism.PeriodIntegrals.HeisDefs

namespace PI

def HeisNorm : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (A : ℝ) (x z : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ),
    ‖UG A x G z‖ ^ 2 * Real.exp (-Real.pi * (HfG A z z).re) =
      ‖G (z + x)‖ ^ 2 * Real.exp (-Real.pi * (HfG A (z + x) (z + x)).re)

end PI
