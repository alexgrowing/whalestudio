import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountRhoPArithStatement

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in

def onDom {r : ℕ} (X : Data E r) (f : Frame X.Ψ r → ℂ) : Frame X.Ψ r → ℂ :=
  fun x => if x ∈ X.dom then f x else 0

def spanDom {r : ℕ} (X : Data E r) (S : Set (Frame X.Ψ r → ℂ)) : Submodule ℂ (Frame X.Ψ r → ℂ) :=
  Submodule.span ℂ (onDom X '' S)

def ZcM {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) : Submodule ℂ (Frame X.Ψ r → ℂ) :=
  spanDom X {g | ∃ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), ∃ θ ∈ X.SS (Xa.Fp + nd X • Xa.L),
    g = fun x => monoM X Fl.s α x * θ x}

def CountRhoPMStatement : Prop :=
  CuspSectionsUpperCount (E := E) → CuspSectionsLowerCount (E := E) →
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → OrderAt X Xa Fl →
    InterpCStatement (E := E) →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + (1 + Xa.c1 / Xa.a1) * leviO X x0 Xa.ps0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∃ C : ℝ, ∀ x ∈ X.dom, Xa.ps0 x ≤ C) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    ModeHalfStatement X →
    ((Module.finrank ℂ (spanDom X (X.SS (Xa.Fp + Xa.T • Xa.L))) : ℝ) -
        Module.finrank ℂ (spanDom X (X.SSgt (Xa.Fp + Xa.T • Xa.L) Xa.c1))) ≤
      (nd X : ℝ) * (nd X + 6) * Module.finrank ℂ (spanDom X (X.SS (Xa.Fp + Xa.T • Xa.L))) / Xa.T

def CountRhoMStatement : Prop :=
  CuspSectionsUpperCount (E := E) → CuspLeadingIndependent (E := E) →
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → OrderAt X Xa Fl →
    InterpCStatement (E := E) →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + (1 + Xa.c1 / Xa.a1) * leviO X x0 Xa.ps0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∃ C : ℝ, ∀ x ∈ X.dom, Xa.ps0 x ≤ C) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    ModeHalfStatement X →
    (Module.finrank ℂ (ZcM X Xa Fl) : ℝ) ≤
      22 * (nd X : ℝ) ^ 2 * Module.finrank ℂ (spanDom X (X.SS (Xa.Fp + Xa.T • Xa.L))) / Xa.T

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
