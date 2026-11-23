import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionProduct.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A B C : HermLine ι) (n j τ : ℕ) (s t : Ω),
    (τ : ℤ) • C.a = (n : ℤ) • A.a + (j : ℤ) • B.a →
    (∀ z ∈ mcPts (mCoordIdeal y), C.h z ^ τ = A.h z ^ n * B.h z ^ j) →
    s ∈ chartLat y A.a n → t ∈ chartLat y B.a 1 →
    s * t ^ j ∈ chartLat y C.a τ ∧
      ∀ c c' : ℝ, IsBoundedH (mCoordIdeal y) y A n c s → IsBoundedH (mCoordIdeal y) y B 1 c' t →
        IsBoundedH (mCoordIdeal y) y C τ (c * c' ^ j) (s * t ^ j)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
