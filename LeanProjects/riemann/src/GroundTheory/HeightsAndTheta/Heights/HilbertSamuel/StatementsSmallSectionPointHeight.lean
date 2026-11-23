import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SmallSectionPointHeight.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (τ : ℕ) (s : Ω) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    1 ≤ τ → s ∈ chartLatNm y A.a τ → s ≠ 0 → IsSmallH (mCoordIdeal y) y A τ s →
    ∃ f : MRing ι, (∃ d, IsMultiHomog f d) ∧ f ∉ mCoordIdeal y ∧
      ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal y ≤ W → f ∉ W → 0 ≤ II K ι W 1 ![A]

theorem SmallSectionPointHeight.chartLat_le_chartLatNm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := by
  intro s hs c hc
  have h := hs c hc
  exact (mem_integralClosure_iff _ _).mpr (isIntegral_algebraMap (x := (⟨_, h⟩ : chartRingZ y c)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
