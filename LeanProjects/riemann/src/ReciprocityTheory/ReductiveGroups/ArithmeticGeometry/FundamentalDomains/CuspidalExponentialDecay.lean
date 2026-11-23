import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def epStar (M f w k0 : ℝ) : ℝ := min 1 (Real.pi / (M * (f * w + 2) * k0 * Real.log 2))

def CuspFormGapCondition : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
    ∃ c' : ℝ, 0 < c' ∧ P ∈ X.SSgt la c'

def CuspidalExponentialDecay : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (c : ℝ), 0 ≤ c → P ∈ X.SSgt la c →
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ C * Real.exp (-2 * Real.pi * c / X.firstMinimumSq x)

def MahlerCompactnessCriterion : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ K : Set (Frame X.Ψ r), IsCompact K ∧ K ⊆ X.dom ∧
    ∀ x ∈ X.dom, ε ≤ X.la1 x → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ K

def MaxBoundStatement : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (M w : ℝ), P ∈ X.SS la →
    0 < M → (∑ τ, X.spread la τ) ≤ w → 0 < w →
    (∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧
        ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) →
    ∀ z0 ∈ X.dom, (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
    ∀ v ∈ X.L', v ≠ 0 → ∃ τ : X.Ψ, epStar M (fdeg E) w X.k0 ≤ X.maj z0 τ (Data.emb τ.1 v)

end

end ReciprocityTheory.ChartRestriction.G.FD
