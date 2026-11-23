import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagOffUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

section Defs

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

def dualMinor (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (k k' : κ) : Ω :=
  φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1)

def lineMinor (k k' : κ) : MRing (T.wwIdx ι ν κ) :=
  X ⟨.line0, k⟩ * X ⟨.line1, k'⟩ - X ⟨.line0, k'⟩ * X ⟨.line1, k⟩

def IsDualFrameAt (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (W : Ideal (MRing (T.wwIdx ι ν κ))) (i : ι) (l : ν) (k k' : κ) : Prop :=
  (X ⟨.base, i⟩ : MRing (T.wwIdx ι ν κ)) ∉ W ∧ (X ⟨.det, l⟩ : MRing (T.wwIdx ι ν κ)) ∉ W ∧
    ∃ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg (N + 3) 0) ∧
      aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * δ l * dualMinor e φ k k') ∧ F ∉ W

end Defs

section Statements

def DiagOffFrame.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ W : Ideal (MRing (T.wwIdx ι ν κ)), W.IsPrime → IsRelevant W → T.wwIdeal x δ e φ (a 0) (a 1) ≤ W →
      ∃ (i : ι) (l : ν) (k k' : κ), IsDualFrameAt x δ e φ (a 0) (a 1) W i l k k'

def DiagOffMinor.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
    (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
    ∀ a : Fin 2 → Φ, AlgebraicIndependent Ω a →
    ∀ W : Ideal (MRing (T.wwIdx ι ν κ)), W.IsPrime → IsRelevant W → T.wwIdeal x δ e φ (a 0) (a 1) ≤ W →
    ∀ (i : ι) (l : ν) (k k' : κ), IsDualFrameAt x δ e φ (a 0) (a 1) W i l k k' →
      lineMinor k k' ∈ W → T.wwIdeal x δ e φ (a 0) (a 0) ≤ W

end Statements

section Inhabit

end Inhabit

end

end GroundTheory.Heights₂.Heights.Inter
