import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def NmSectionsFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → Birational y → ∀ τ₂ : ℕ,
    ∃ (J : Type) (_ : Fintype J) (d : J → ℕ) (e : J → Ω) (τ₁ : ℕ),
      (∀ j, τ₂ ≤ d j ∧ d j ≤ τ₁ ∧ e j ∈ chartLatNm y (fun k => (a k : ℤ)) (d j)) ∧
      ∀ τ : ℕ, τ₁ ≤ τ → ∀ s ∈ chartLatNm y (fun k => (a k : ℤ)) τ,
        ∃ r : J → Ω, (∀ j, r j ∈ secM y (fun k => (τ - d j) * a k)) ∧ s = ∑ j, r j * e j

end GroundTheory.Heights₂.Heights.HilbertSamuel
