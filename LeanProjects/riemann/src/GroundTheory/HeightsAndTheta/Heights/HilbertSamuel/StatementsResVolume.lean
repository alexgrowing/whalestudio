import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def ResVolume.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ)
    (R : AnRes P J e) [MeasurableSpace R.X] [BorelSpace R.X],
    IsArithVar P (e + 1) → ∃ dV : Measure R.X, IsSmoothVolume R.A dV

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
