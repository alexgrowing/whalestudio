import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

variable {p : ℕ} [Fact p.Prime]

def IntC (G : HTGroup p) (w : AwayP p) (a : w.1.adicCompletion ℚ ⊗[ℚ] G.C) : Prop :=
  ∀ i, coordL G w a i ∈ w.1.adicCompletionIntegers ℚ

end GlobalTheory.FinClsLoc
