import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ChartSpec

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open GlobalTheory.CompanionTheory.Ar.Deg (vdeg rootPair)
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.LowerWeightVolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def volConst (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : ℝ :=
  ((nd X).factorial : ℝ) * (Real.pi ^ nd X)⁻¹ * (muF X x0 FF).toReal

def vol (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (v : X.Ψ → Fin r → ℝ) : ℝ :=
  volConst X x0 FF * vdeg X v

def upperWt (X : Data E r) (Xa : ArchInM X) : X.Ψ → Fin r → ℝ := fun τ i => (Xa.L τ i : ℝ)

def lowerWt (X : Data E r) (Xa : ArchInM X) (a : ℕ) : X.Ψ → Fin r → ℝ :=
  fun τ i => (Xa.L τ i : ℝ) - (a : ℝ) / 2 * (Xa.de τ i : ℝ)

def DegreeBounds (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (a : ℕ),
    (∀ γ ∈ X.Γ, X.χ (kapW X) γ = 1) →
    1 ≤ a → 0 < Xa.rr →
    X.IsDominant Xa.L → X.IsDominant ((2 : ℕ) • Xa.L - a • Xa.de) →
    ∀ x0 : Frame X.Ψ r, IsOrth X x0 →
      (∃ FF : Set (V (nd X)), IsFundSet X x0 FF) ∧
      ∀ FF : Set (V (nd X)), IsFundSet X x0 FF →
        muF X x0 FF < ⊤ ∧
        vol X x0 FF (lowerWt X Xa a) ≤ (Fl.δ : ℝ) ∧
        (Fl.δ : ℝ) ≤ vol X x0 FF (upperWt X Xa)

end GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.LowerWeightVolume
