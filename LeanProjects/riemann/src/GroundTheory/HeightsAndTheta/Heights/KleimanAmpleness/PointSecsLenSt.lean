import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CycleSplit.PointSecs.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (K : Type w) [Field K] [Algebra S K] (N : ℕ) (y : Fin (N + 1) → K),
    (∃ i, (X i : Poly S N) ∉ primeOf (S := S) y) → ringKrullDim (Poly S N ⧸ primeOf (S := S) y) ≤ 1 →
    ∀ (Q₁ Q₂ : LineBundle S y) (c₁ c₂ : ℤ),
      Module.length S (Q₁.twist (twistSys S y c₁)).secs = Module.length S (Q₂.twist (twistSys S y c₂)).secs

end

end GroundTheory.Heights₂.Heights.Kleiman
