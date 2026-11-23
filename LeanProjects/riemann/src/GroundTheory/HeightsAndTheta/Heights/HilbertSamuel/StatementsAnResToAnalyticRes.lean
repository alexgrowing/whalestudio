import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConeAnalyticSubset
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory
open scoped Manifold ContDiff

noncomputable section

def AnResToAnalyticRes.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : T2Space M) (_ : CompactSpace M)
      (_ : ChartedSpace (Fin D → ℂ) M) (_ : IsManifold 𝓘(ℂ, Fin D → ℂ) ∞ M)
      (_ : MeasurableSpace M) (_ : BorelSpace M) (f : M → Ix κ → ℂ) (dV : Measure M),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.IsAnalyticRes (coordIdeal ℤ d.x) D f ∧
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.IsSmoothVolume D dV ∧
      (∀ n : ℕ, chi d.x d.m (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure f dV) n = resChi d n) ∧
      ∀ (n : ℕ) (g : MvPolynomial (Ix κ) ℤ), g.IsHomogeneous n →
        l2Norm d.m (Int.castRingHom ℂ) (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure f dV) n g =
          resolutionSectionL2Norm d n g

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
