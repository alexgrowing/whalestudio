import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def NmSectionsRational.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → Birational y → KH.NormalGenericFibre y →
    ∃ τ₀ : ℕ, ∀ τ : ℕ, τ₀ ≤ τ → ∀ s ∈ chartLatNm y (fun k => (a k : ℤ)) τ,
      ∃ m : ℕ, 1 ≤ m ∧ (m : Ω) * s ∈ secM y (fun k => τ * a k)

end GroundTheory.Heights₂.Heights.HilbertSamuel
