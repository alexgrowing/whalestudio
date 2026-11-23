import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl

set_option autoImplicit false

namespace GlobalTheory.Vert.Model.FlagPair

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : GlobalTheory.Vert.Model O}
  {E E' : Z.X.Modules} {φ : Z.GenIso E E'} {N : ℕ}

def Adj (P P' : GlobalTheory.Vert.Model.FlagPair φ N) : Prop :=
  ∃ j : Fin (N + 1), ∀ i, i ≠ j → P.fl.SameStep P'.fl i ∧ P.fl'.SameStep P'.fl' i

end GlobalTheory.Vert.Model.FlagPair
