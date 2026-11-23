import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def NfacRmulStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
    X.nfac la (rmul x b) = ‖bchar la b‖⁻¹ * X.nfac la x

def NfacLactStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, X.nfac la (lact γ x) = X.nfac la x

def PnormInvStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
    ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      X.pnorm la P (lact γ (rmul x b)) = X.pnorm la P x

def KapGGStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 x1 : Frame X.Ψ r) (γ : GL (Fin r) E) (U : Set (V (nd X)))
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r), IsOpen U → DifferentiableOn ℂ Φ U →
    (∀ z ∈ U, cpt X x0 z ∈ X.dom ∧ bf z ∈ Bor X.Ψ r ∧
      cpt X x0 z = lact γ (rmul (cpt X x1 (Φ z)) (bf z))) →
    ∀ z ∈ U, (fderiv ℂ Φ z).det = bchar (kapW X) (bf z)

def CurvGGStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x0 : Frame X.Ψ r) (z : V (nd X)), cpt X x0 z ∈ X.dom →
    (X.IsDominant la → ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re) ∧
    (IsStrictDom X la → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re)

def LineBundleFirstBoundGlobalGeneration : Prop :=
  ∀ (r : ℕ) (X : Data E r), 0 < r →
    (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.la1 (lact γ (rmul x b)) = X.la1 x) ∧
    ContinuousOn X.la1 X.dom ∧ ∀ x ∈ X.dom, 0 < X.la1 x

end

end ReciprocityTheory.ChartRestriction.G.AR.Inst
