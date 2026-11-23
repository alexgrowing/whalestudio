import Formalism.SharpRestriction.DesignExistsOfChoices
import Development.AutomorphicArithmetic.CharacterBoxes.Supply

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX

def ExS (𝒜 : FamClass) (cT : ℝ → ℝ → ℝ) : Prop :=
  ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    Formalism.MainNotions.DesignChoices (Formalism.MainNotions.WithTw fun Fm => 𝒜 Fm ∧ G.cls la Fm) 3 cT

end UpperTheory.Top

end
