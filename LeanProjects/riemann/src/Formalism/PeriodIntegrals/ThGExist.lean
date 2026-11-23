import Formalism.PeriodIntegrals.ThGDefs

namespace PI

def ThGExist : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La' : AddSubgroup (T → I → J → ℂ), GoodLat s A La' →
      ∃ G ∈ ThSpG s A La', G ≠ 0

end PI
