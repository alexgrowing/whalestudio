import Formalism.PeriodIntegrals.HeisDefs

namespace PI

def HeisPull : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (A : ℝ) (ψ : (T → I → J → ℂ) ≃ₗ[ℂ] (T → I → J → ℂ)),
    (∀ z w, HfG A (ψ z) (ψ w) = HfG A z w) → ∀ (x : T → I → J → ℂ) (F : (T → I → J → ℂ) → ℂ),
      (fun z => UG A x F (ψ z)) = UG A (ψ.symm x) (fun z => F (ψ z))

end PI
