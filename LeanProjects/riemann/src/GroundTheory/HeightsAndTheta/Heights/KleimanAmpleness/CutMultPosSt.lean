import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u

def CutMultPos.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (J qq : Ideal (Poly S N))
    (h : qq ∈ J.minimalPrimes),
    haveI : qq.IsPrime := h.1.1
    0 < cutMult J qq ∧ cutMult J qq < ⊤

end

end GroundTheory.Heights₂.Heights.Kleiman
