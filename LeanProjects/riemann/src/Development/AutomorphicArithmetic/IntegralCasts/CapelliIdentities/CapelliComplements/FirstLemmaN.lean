import Mathlib

namespace Bl.FirstLemmaN

noncomputable def goal1 :
  {n : Nat} → Matrix (Fin n) (Fin n) Complex → Prop := fun {n} A =>
  (∀ i j : Fin n, i < j → A i j = 0) ∧ ∀ i : Fin n, A i i = 1

end Bl.FirstLemmaN
