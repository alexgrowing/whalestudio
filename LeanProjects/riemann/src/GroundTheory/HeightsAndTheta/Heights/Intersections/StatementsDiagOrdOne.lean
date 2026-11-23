import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def DiagOrdOne.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ (n : ℕ) (g h : MRing (T.wwIdx ι ν κ)), IsMultiHomog g (T.wwDeg n 1) →
      IsMultiHomog h (T.wwDeg (n + 3) 0) → h ∉ T.wwIdeal x δ e φ (a 0) (a 1) →
      aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h →
        multAt (T.wwIdeal x δ e φ (a 0) (a 1) ⊔ Ideal.span {g}) (T.wwIdeal x δ e φ (a 0) (a 0)) = 1

end

end GroundTheory.Heights₂.Heights.Inter
