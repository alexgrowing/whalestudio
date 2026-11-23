import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockCoeffCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockHorizDiv.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ)
    (l : Ix κ → ℤ),
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), IsHorizontal W →
      (W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) ↔
          W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c)) ∧
        (W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) →
          multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}) W =
            multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
