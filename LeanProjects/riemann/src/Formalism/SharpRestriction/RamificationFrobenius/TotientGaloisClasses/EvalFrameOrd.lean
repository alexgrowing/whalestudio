import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

@[positivity Formalism.HC.Frame.ord _]
def evalFrameOrd : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with
  | none => throwError "no order"
  | some _pα => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Formalism.HC.Frame.ord $a) =>
    assertInstancesCommute
    return .positive q(Formalism.HC.Frame.ord_pos $a)
  | _, _, _ => throwError "not the order of a frame"

end Mathlib.Meta.Positivity
