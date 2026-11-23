import Formalism.LocalRingCardinality.DataParams₂

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

def DFam : Type 1 := ∀ ε : ℝ, 0 < ε → ε < 1 / 52 → Fam ε

end Formalism.MainNotions

end
