import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def PerturbMonomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (q : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (A.a = fun k => (a k : ℤ)) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → MonomialsBounded (mCoordIdeal y) A a →
    1 ≤ q →
    IsSmallGeneratedDatum P0 y D (HermLine.zcomb A (fsH ι) q 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
