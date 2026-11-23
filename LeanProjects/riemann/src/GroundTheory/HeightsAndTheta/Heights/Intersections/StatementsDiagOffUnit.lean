import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def DiagOffUnit.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ W : Ideal (MRing (T.wwIdx ι ν κ)), W.IsPrime → IsRelevant W → T.wwIdeal x δ e φ (a 0) (a 1) ≤ W →
      ¬ T.wwIdeal x δ e φ (a 0) (a 0) ≤ W →
      ∃ (α β : T.WBlk → ℕ) (u v : MRing (T.wwIdx ι ν κ)), IsMultiHomog u α ∧ IsMultiHomog v β ∧
        (∀ k, α k + T.wwDeg 0 1 k = β k + T.wwDeg 3 0 k) ∧ u ∉ W ∧ v ∉ W ∧
        aeval (T.wwCoord x δ e φ (a 0) (a 1)) u * T.diagSec a = aeval (T.wwCoord x δ e φ (a 0) (a 1)) v

end

end GroundTheory.Heights₂.Heights.Inter
