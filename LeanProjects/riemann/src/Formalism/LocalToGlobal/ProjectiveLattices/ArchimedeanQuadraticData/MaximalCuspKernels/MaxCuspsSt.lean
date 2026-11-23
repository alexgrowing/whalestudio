import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

noncomputable section

namespace Formalism.L2.Pj.QAt

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

def hq (χ : Matrix (Fin ρ) (Fin ρ) E) (η : Fin ρ → E) : E :=
  ∑ a, ∑ b, η a * χ a b * cc (η b)

def IsExpoFD (X : Data E r) (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E) : Prop :=
  IsHermE χ ∧ ∀ k, ∃ z : ℤ, phZ X cu χ k = z

def KilledFD (X : Data E r) (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E) (c : ℝ) : Prop :=
  ∃ η : Fin ρ → E, η ≠ 0 ∧ (∑ a, η a • cu.e a) ∈ X.Λ ∧ ∑ τ : X.Ψ, (τ.1 (hq χ η)).re ≤ c

def MaxCuspsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r),
    (∀ ξ, X.IsIso ξ → ∃ cu : CuspFD X ρ, ξ ∈ Submodule.span E (Set.range cu.e)) →
    (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) →
    ∀ (la : Wt X.Ψ r),
    (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ,
      (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) →
    ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
      (P ∈ X.SSgt la c ↔
        ∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c →
          ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0)

end Formalism.L2.Pj.QAt
