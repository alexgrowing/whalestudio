import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.QuotientIsHausdorff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (K : Type) [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

def delG (D : ℕ) {N : ℕ} (x : Fin (N + 1) → Ω) : ℕ :=
  Module.finrank (IntermediateField.adjoin K (Set.range
    (ReciprocityTheory.ChartRestriction.G.T0.sImg (D := D) (0 : Fin (N + 1)) (fun k : Fin N => x k.succ / x 0))))
    (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)

variable {K}

def GenOver (σ : K →+* ℂ) {I : Type} (t : I → ℂ) : Prop :=
  ∀ Q : MvPolynomial I K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0

def OnCone (σ : K →+* ℂ) {N : ℕ} (x : Fin (N + 1) → Ω) (v : Fin (N + 1) → ℂ) : Prop :=
  ∀ (Q : MvPolynomial (Fin (N + 1)) K) (d : ℕ), Q.IsHomogeneous d → MvPolynomial.aeval x Q = 0 →
    MvPolynomial.eval₂ σ v Q = 0

def IsAtPt {N : ℕ} (x : Fin (N + 1) → Ω) (P : Ω →+* ℂ) (v : Fin (N + 1) → ℂ) : Prop :=
  v 0 ≠ 0 ∧ ∀ j, v j = P (x j / x 0) * v 0

def FnTie (σ : K →+* ℂ) (X : Data E r) {N : ℕ} (x : Fin (N + 1) → Ω) (w : Fin (N + 1) → Frame X.Ψ r → ℂ) : Prop :=
  x 0 ≠ 0 ∧ IntermediateField.adjoin K (Set.range fun j => x j / x 0) = ⊤ ∧
  (∀ y ∈ X.dom, (∃ j, w j y ≠ 0) ∧ OnCone σ x fun j => w j y) ∧
  ∀ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = σ →
    (∃ y ∈ X.dom, IsAtPt x P fun j => w j y) ∧
    ∀ y ∈ X.dom, ∀ y' ∈ X.dom, (IsAtPt x P fun j => w j y) → (IsAtPt x P fun j => w j y') →
      ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y' = lact γ (rmul y b)

end GlobalTheory.CompanionTheory.Ar.Deg
