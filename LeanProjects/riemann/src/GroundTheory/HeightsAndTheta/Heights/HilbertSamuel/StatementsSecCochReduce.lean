import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsReductionComplex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SecCochReduce.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (p : ℕ) (a : K → ℤ),
    ∀ s ∈ chartLat y a 1,
      FibreReduction.redCoch y p 0 (GenOnFibres.secCoch y ℤ s a) = GenOnFibres.secCoch y (ZMod p) s a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
