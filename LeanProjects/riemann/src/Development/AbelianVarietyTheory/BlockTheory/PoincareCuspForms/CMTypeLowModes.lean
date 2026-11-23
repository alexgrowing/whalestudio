import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMTypeLowModes

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def FinMu (X : Data E r) : Prop :=
  ∀ x0 : Frame X.Ψ r, IsOrth X x0 → ∀ FF : Set (V (nd X)), IsFundSet X x0 FF → muF X x0 FF < ⊤

def IsInvariant (X : Data E r) (ps : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ps (rmul x b) = ps x) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ps (lact γ x) = ps x

def TwoBounds (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ,
    (∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)) ∧
    ∀ η : ℝ, 0 < η → ∃ Cη : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
      (∀ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
      ps x ≤ Cη + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ : X.Ψ, X.tt ξ x τ

def PointBound (X : Data E r) (la : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x → ∀ M : ℝ,
    (∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom → ps (cpt X x z) ≤ M) →
    X.pnorm la P x ≤ C * Real.exp (M / 2)

def NoModesBelow (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (a : ℝ) : Prop :=
  ∀ ξ : Fin r → E, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∑ τ, ν τ < a → ∀ x ∈ X.dom, X.fj la ξ ν P x = 0

def LowModes (X : Data E r) : Prop :=
  ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ps : Frame X.Ψ r → ℝ) (a : ℝ), 0 ≤ a →
    X.IsSec la P → IsInvariant X ps → TwoBounds X ps a → PointBound X la ps P →
    NoModesBelow X la P a

def Inputs (X : Data E r) : Prop := FinMu X ∧ LowModes X

def InputsStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r), Inputs X

end

end GlobalTheory.IndefiniteRowSideFullHecke.CMTypeLowModes
