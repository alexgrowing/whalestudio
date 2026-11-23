import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrderOfEqMaxTwoOfSignNegImplicit
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderOf_eq_max_two_of_sign_neg_implicit : ∀ {fr : Formalism.HC.Frame} (φ : fr.GG), φ.1.2 = -1 → orderOf φ = Nat.lcm 2 (orderOf φ.2) := by
  first | exact @GlobalTheory.orderOf_moving_stmt | exact GlobalTheory.orderOf_moving_stmt | (intros; apply GlobalTheory.orderOf_moving_stmt <;> assumption)
