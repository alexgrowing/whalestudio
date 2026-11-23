import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG

noncomputable section
open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.QuantumDeterminants Formalism.MainNotions.OnePlaceEstimates
namespace GlobalTheory.Core.Deg

def DiscreteSeriesDegreeBound : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : TensorDS n ε μ H σ) (h : ℝ),
    IsHCParam μ → IsDS ε μ σ → GapAtLeast ε μ h → Formalism.MainNotions.GapDS.thrX ε + 2 < h →
    1 ≤ Formalism.MainNotions.PlaceDegreeData.pOf ε → 1 ≤ Formalism.MainNotions.PlaceDegreeData.qOf ε →
    ∀ s ∈ X.Sm, ∀ (v : H) (vs : X.Hs s), v ≠ 0 → vs ≠ 0 →
      fdegOf (Formalism.REAL.muG ε) (X.σs s) vs / fdegOf (Formalism.REAL.muG ε) σ v =
        ∏ s' ∈ Finset.univ.erase s, (μ s + 1 - μ s') / (μ s - μ s')
end GlobalTheory.Core.Deg
