import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerHeightsirational.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, w j ∈ chartLat y a 1) →
    KH.GeneratesOn y a w → 0 < genDeg (mCoordIdeal y) D a →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (N : ℕ) (v : Fin N → Ω), AddSubgroup.closure (Set.range v) = chartLat y a m →
      BlockBirational (addBlock y v) (none : Option K)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
