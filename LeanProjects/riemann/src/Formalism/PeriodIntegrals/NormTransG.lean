import Formalism.PeriodIntegrals.ThGDefs

namespace PI

def NormTransG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La' : AddSubgroup (T → I → J → ℂ), GoodLat s A La' → ∀ F ∈ ThSpG s A La', ∀ x : T → I → J → ℂ,
      normSqG A La' (UG A x F) = normSqG A La' F

end PI
