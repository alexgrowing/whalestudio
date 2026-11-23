import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionPointHeight
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SectionOrderAtPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (s : Ω) (W : Ideal (MRing ι)) (G H : MRing ι)
    (dg dh : K → ℕ),
    IsArithVar W 1 → mCoordIdeal y ≤ W → s ∈ chartLatNm y a τ →
    IsMultiHomog G dg → IsMultiHomog H dh → (∀ k, (dg k : ℤ) = dh k + τ * a k) →
    aeval y G = s * aeval y H → G ∉ W → H ∉ W →
    ∀ V ∈ divSupp W H, V ∈ divSupp W G ∧
      multAt (W ⊔ Ideal.span {H}) V ≤ multAt (W ⊔ Ideal.span {G}) V

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
