import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjFrameGraphChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TranscRatioDeg.Statement : Prop :=
  ∀ (ι : Type) (E : Type) [Field E] [CharZero E] (u : ι → E) (D : ℕ) (e : Fin (D + 1) → ι) (w : Fin (D + 1) → E)
    (i₀ : ι) (Φ : Type) [Field Φ] [Algebra Φ E],
    u i₀ ≠ 0 → (∀ k, u (e k) ≠ 0) → (∀ k, w k * u (e 0) = w 0 * u (e k)) →
    Transcendental (Algebra.adjoin ℤ (Set.range u)) (w 0) →
    (algebraMap Φ E).fieldRange = Subfield.closure (Set.range w) →
    Module.finrank Φ (IntermediateField.adjoin Φ (Set.range fun i => u i / u i₀)) = projDeg u e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
