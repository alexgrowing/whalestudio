import Formalism.PeriodIntegrals.WPhDefs

namespace PI

open WPhDefs

def WOnLatG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)), QIntLat s A La' →
    ∀ p : ℕ, p.Prime → ∀ x ∈ La', wPhG s A p x = alG s A x

end PI
