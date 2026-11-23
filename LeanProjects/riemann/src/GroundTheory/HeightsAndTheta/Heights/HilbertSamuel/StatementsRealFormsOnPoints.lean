import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsBoundedAtOfIsBoundedH
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RealFormsOnPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (d : ℕ) (e : K → ℕ) (r : ℕ) (g : Fin r → MRing ι),
    IsArithVar (mCoordIdeal y) d → (∀ i, IsMultiHomog (g i) e) →
    LinearIndependent ℤ (fun i => aeval y (g i)) →
    ∀ c : Fin r → ℝ,
      (∀ z ∈ mcPts (mCoordIdeal y), ∑ i, (c i : ℂ) * eval z (map (Int.castRingHom ℂ) (g i)) = 0) →
      c = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
