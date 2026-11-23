import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FSScaled
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel MvPolynomial

noncomputable section

def SmallFormsFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) →
    ∀ (m : ℕ) (R : ℝ), {σ : Ω | σ ∈ secM y (fun _ => m) ∧
      ∀ g : MRing ι, IsMultiHomog g (fun _ => m) → aeval y g = σ →
        ∀ z ∈ mcPts (mCoordIdeal y), ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ R * (fsH ι).h z ^ m}.Finite

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
