import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.ZnNonneg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow

namespace PIW.FdPA

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory

noncomputable section

theorem fourierJacobi_differentiable {E : Type} [Field E] [NumberField E] [IsCMField E] : FjDiff E := by
  intro r X la P ξ ν hP hξ
  exact CuspCoefficientFlow.fj_diffOn (X := X) la P hP hξ ν

theorem fourierJacobi_bounded {E : Type} [Field E] [NumberField E] [IsCMField E] : FjBdd E := by
  intro r X la P ξ ν hP hξ
  obtain ⟨-, C, hC⟩ := hP
  exact ⟨C, fun x hx => FlowCoefficientBounds.fj_bound (X := X) la P C hC hξ ν hx⟩

theorem fourierJacobi_boundaryEq {E : Type} [Field E] [NumberField E] [IsCMField E] : FjBEq E := by
  intro r X la P ξ ν hP hξ x hx b hb
  classical
  have hflow : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) (rmul x b) =
      rmul (X.flow ξ (fun τ => (s τ : ℂ)) x) b := by
    intro s
    funext τ
    show X.flowMat ξ τ (s τ : ℂ) * (mat x τ * mat b τ) = X.flowMat ξ τ (s τ : ℂ) * mat x τ * mat b τ
    rw [Matrix.mul_assoc]
  have hP' : ∀ s : X.Ψ → ℝ,
      P (X.flow ξ (fun τ => (s τ : ℂ)) (rmul x b)) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) =
        bchar la b * (P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
          cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)) := by
    intro s
    rw [hflow, hP.2.1 _ (FlowCoefficientBounds.flow_real X hξ hx s la).1 b hb, mul_assoc]
  unfold Data.fj
  split_ifs with h1 h2
  · simp_rw [hP']
    rw [integral_const_mul]
    ring
  · simp
  · simp

end

end PIW.FdPA
