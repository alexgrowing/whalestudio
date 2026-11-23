import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def JetInjAt {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) : Prop :=
  ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L), VanS X Fl.xs Fl.s (Xa.T + nd X + 7) f → ∀ x ∈ X.dom, f x = 0

def CuspFormsJetInjectiveCount : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), JetInjAt X Xa Fl →
    ∀ (rr : ℕ) (f : Fin rr → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Xa.Fp + Xa.T • Xa.L)) →
      (∀ a : Fin rr → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0) →
      rr ≤ Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X)

end ReciprocityTheory.ChartRestriction.G.AR.Up
