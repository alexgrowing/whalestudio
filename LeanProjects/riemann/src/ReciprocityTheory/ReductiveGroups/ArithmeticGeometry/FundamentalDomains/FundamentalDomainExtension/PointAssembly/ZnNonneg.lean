import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting

namespace PIW.FdPA

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric

noncomputable section

def FjDiff (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ),
    X.IsBddSec la P → X.IsIso ξ → DifferentiableOn ℂ (X.fj la ξ ν P) X.dom

def FjBEq (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ),
    X.IsSec la P → X.IsIso ξ → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      X.fj la ξ ν P (rmul x b) = bchar la b * X.fj la ξ ν P x

def FjBdd (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ),
    X.IsBddSec la P → X.IsIso ξ → ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la (X.fj la ξ ν P) x ≤ C

def OrthoDom (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), X.IsOrtho x → x ∈ X.dom

def UnitDom (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r),
    X.IsUnitaryC n → x ∈ X.dom → X.lmulC n x ∈ X.dom

def BorFlag (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x b : Frame X.Ψ r), b ∈ Bor X.Ψ r → rmul x b ∈ X.dom →
    X.SameFlag x (rmul x b)

def ZnSmul (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (t : ℂ) (Z : X.Coord), X.zN (t • Z) = ‖t‖ * X.zN Z

def ZnNonneg (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Z : X.Coord), 0 ≤ X.zN Z

def NfacPos (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r), x ∈ X.dom → 0 < X.nfac la x

def XZZero (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), X.xZ x 0 = x

end

end PIW.FdPA
