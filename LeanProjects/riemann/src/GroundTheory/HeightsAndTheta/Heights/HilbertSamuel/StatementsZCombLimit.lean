import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ZCombLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A B : HermLine ι) (II : IntersectionSystem) (k : ℕ),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → IsSmoothHerm A → IsSmoothHerm B →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p q : ℕ, 0 < p → 0 < q → (p : ℝ) / q < δ →
      |II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A B ((q : ℤ) - k * p) p) /
          (q : ℝ) ^ (D + 1) - II K ι (mCoordIdeal y) (D + 1) (fun _ => A)| < ε ∧
      |(genDeg (mCoordIdeal y) D (HermLine.zcomb A B ((q : ℤ) - k * p) p).a : ℝ) / (q : ℝ) ^ D -
          genDeg (mCoordIdeal y) D A.a| < ε

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
