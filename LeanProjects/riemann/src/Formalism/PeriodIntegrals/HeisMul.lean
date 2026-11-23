import Formalism.PeriodIntegrals.HeisDefs

namespace PI

def HeisMul : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (A : ℝ) (x y : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ),
    UG A x (UG A y G) =
      fun z => Complex.exp (-((Real.pi : ℂ) * Complex.I) * ((HfG A x y).im : ℂ)) * UG A (x + y) G z

end PI
