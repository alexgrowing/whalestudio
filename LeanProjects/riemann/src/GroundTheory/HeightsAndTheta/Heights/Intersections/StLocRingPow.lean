import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.LocRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingPow.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s t : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (x : FractionRing (MRing ι ⧸ P))
    (u v : MRing ι) (b : K → ℕ) (y : FractionRing (MRing ι ⧸ P)),
    P.IsPrime → IsMultiHomogIdeal P → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsMultiHomog t a → t ∉ W → x * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) →
    IsMultiHomog u b → IsMultiHomog v b → u ∈ W → v ∉ W → y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) →
    ∃ n : ℕ, ∃ z ∈ locRing P W, y ^ n = x * z

end

end GroundTheory.Heights₂.Heights.Inter
