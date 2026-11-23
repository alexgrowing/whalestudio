import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.SymbolExtensionProperty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M

def FLBoundOfGoodS.Statement : Prop :=
  ∀ (D : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (A : FinHolAtlas D X) (d : IndefiniteRowSideFullHecke.EffectiveHS.FSData A Y) (s : Fin D → Fin d.W.n → ℂ),
    d.IsGoodS s → FLBound A d.W.e (fun i => d.W.sec (s i))

end GroundTheory.Heights₂.Heights.EffectiveHS
