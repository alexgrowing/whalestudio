import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerBlockArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (m N : ℕ) (v : Fin N → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, v j ∈ chartLat y a m) →
    KH.GeneratesOn y (fun k => (m : ℤ) * a k) v → IsArithVar (mCoordIdeal (addBlock y v)) (D + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
