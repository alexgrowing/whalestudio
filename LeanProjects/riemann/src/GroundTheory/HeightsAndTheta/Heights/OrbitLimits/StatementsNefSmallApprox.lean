import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNefCountUpper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def NefSmallApprox.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    NefOnFibres (mCoordIdeal y) A.a → NefOnGeneric (mCoordIdeal y) A →
    HeightsNonneg II (mCoordIdeal y) A →
    ∀ δ : ℝ, 0 < δ → ∃ (q : ℕ) (B : HermLine ι) (P1 : Ideal (MRing ι)), 1 ≤ q ∧
      IsSmallGeneratedDatum P1 y D B ∧ IsConjInvariantH B ∧
      II K ι (mCoordIdeal y) (D + 1) (fun _ => B) ≤
        (q : ℝ) ^ (D + 1) * (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + δ) ∧
      ∀ᶠ n : ℕ in atTop, ∃ t : Ω, t ≠ 0 ∧ ∀ s ∈ chartLat y A.a n, IsSmallH (mCoordIdeal y) y A n s →
        s * t ∈ chartLat y B.a (n / q + 1) ∧ IsSmallH (mCoordIdeal y) y B (n / q + 1) (s * t)

end

end GroundTheory.Heights₂.Heights.Targets
