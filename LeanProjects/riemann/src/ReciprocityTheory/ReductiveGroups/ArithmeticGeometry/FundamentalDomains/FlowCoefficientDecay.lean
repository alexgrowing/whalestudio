import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def CuspCoefficientBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u → (∀ i, u i ∈ X.Λ) →
    ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
    (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) →
    ∀ ν : X.Ψ → ℝ,
      DifferentiableOn ℂ (X.fj la (u 0) ν P) X.dom ∧
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.fj la (u 0) ν P (rmul x b) = bchar la b * X.fj la (u 0) ν P x) ∧
      ∀ b ∈ X.LZ X.g, ∀ x ∈ X.dom, X.fj la (u 0) ν P (X.Zb u b x) = X.fj la (u 0) ν P x

def FlowCoefficientDecay : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ),
    IsotropicFlowSetting X la P ξ ν c1 w z0 x a →
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ, ∀ z ∈ X.dom, X.SameFlag z0 z →
      X.pnorm la (X.fz ![ξ, (X.NC : E) • x] X.g χ (X.fj la ξ ν P)) z ≤
        2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
          sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y}

end

end ReciprocityTheory.ChartRestriction.G.FD
