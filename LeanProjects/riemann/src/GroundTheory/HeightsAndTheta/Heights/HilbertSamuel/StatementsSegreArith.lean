import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def segreCoords {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [CommRing Ω] (y : (Σ k, ι k) → Ω) :
    Ix ((k : K) → ι k) → Ω :=
  fun p => ∏ k, y ⟨k, p.2 k⟩

def SegreArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) →
    IsArithVar (ι := GlobalTheory ((k : K) → ι k)) (coordIdeal ℤ (segreCoords y)) (D + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
