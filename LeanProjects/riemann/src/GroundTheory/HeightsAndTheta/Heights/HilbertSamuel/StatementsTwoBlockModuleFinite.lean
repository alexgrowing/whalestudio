import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockModule
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockPieceCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockModuleFinite.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    IsMultiHomogIdeal (twoBlockMOuter x (matAct B x) c) ∧ IsMultiHomogIdeal (twoBlockMInner x (matAct B x) l) ∧
      twoBlockMInner x (matAct B x) l ≤ twoBlockMOuter x (matAct B x) c ∧
      (∃ N : ℕ, 0 < N ∧ ∀ f ∈ twoBlockMOuter x (matAct B x) c,
        (N : MRing (FinTwoTypeFamily κ)) * f ∈ twoBlockMInner x (matAct B x) l) ∧
      ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), W.IsPrime → twoBlockMInner x (matAct B x) l ≤ W → IsRelevant W →
        ringKrullDim (MRing (FinTwoTypeFamily κ) ⧸ W) ≤ ((D + Fintype.card (Fin 2) : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
