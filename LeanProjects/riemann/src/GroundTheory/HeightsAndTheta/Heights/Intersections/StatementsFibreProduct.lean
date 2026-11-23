import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagPull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Statements

def WWArithVar.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.WWArithVarStatement (Φ := Φ) B e φ δ

def FibreProduct.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω) (D : ℕ) (a : Fin 2 → Φ),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    IsArithVar (T.baseIdeal x) D → AlgebraicIndependent Ω a →
      ((∀ j, IsArithVar (T.yyIdeal x δ e φ (a j)) (D + 1)) ∧
        IsArithVar (T.wwIdeal x δ e φ (a 0) (a 1)) (D + 2)) ∧
      (∀ j : Fin 2, (T.wwIdeal x δ e φ (a 0) (a 1)).comap
          (rename (T.yyEmb j) : MRing (T.yyIdx ι ν κ) →ₐ[ℤ] MRing (T.wwIdx ι ν κ)).toRingHom =
        T.yyIdeal x δ e φ (a j)) ∧
      IsArithVar (T.wwIdeal x δ e φ (a 0) (a 0)) (D + 1) ∧
      ((∀ n : ℕ, (fun k => (T.wwDeg n 1 k : ℤ) - (T.wwDeg (n + 3) 0 k : ℤ)) = T.llDeg) ∧
        2 • T.llDeg = -(T.twoXiDeg 0 + T.twoXiDeg 1)) ∧
      (∃ (n : ℕ) (g h : MRing (T.wwIdx ι ν κ)), IsMultiHomog g (T.wwDeg n 1) ∧
        IsMultiHomog h (T.wwDeg (n + 3) 0) ∧ h ∉ T.wwIdeal x δ e φ (a 0) (a 1) ∧
        aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h) ∧
      (∀ (n : ℕ) (g h : MRing (T.wwIdx ι ν κ)), IsMultiHomog g (T.wwDeg n 1) →
        IsMultiHomog h (T.wwDeg (n + 3) 0) → h ∉ T.wwIdeal x δ e φ (a 0) (a 1) →
        aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h →
          T.toZCycle (divCycle (T.wwIdeal x δ e φ (a 0) (a 1)) g) -
              T.toZCycle (divCycle (T.wwIdeal x δ e φ (a 0) (a 1)) h) =
            Finsupp.single (T.wwIdeal x δ e φ (a 0) (a 0)) 1) ∧
      ∀ (A : HermLine (T.yyIdx ι ν κ)) (A₀ A₁ : HermLine (T.wwIdx ι ν κ)), T.IsHermPull 0 A A₀ →
        T.IsHermPull 1 A A₁ → ∀ z ∈ mcPts (T.wwIdeal x δ e φ (a 0) (a 0)), ∃ c : ℂ, c ≠ 0 ∧
          (∀ k : κ, z ⟨.line1, k⟩ = c * z ⟨.line0, k⟩) ∧ A₁.h z = ‖c‖ ^ A.a .line * A₀.h z

end Statements

section Inhabit

end Inhabit

end

end GroundTheory.Heights₂.Heights.Inter
