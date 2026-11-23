import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable

open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.PoincareSeriesInner.W

universe u

def CplxDC : Prop :=
  ∀ (G : Type u) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S S' : Subgroup G) [Countable Γ], S ≤ Γ → S' ≤ Γ →
  ∀ (D D' : Set G), IsRightTransversal Γ S D → IsRightTransversal Γ S' D' →
  ∀ (R : Set G), IsDoubleTransversal Γ S S' R →
  ∀ (Fs : G → Set G), (∀ r ∈ R, IsFundamentalDomain (stab S S' r) (Fs r) μ) →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (φ ψ : G → ℂ), Measurable φ → Measurable ψ →
    (∀ s ∈ S, ∀ y : G, φ (s * y) = φ y) → (∀ s ∈ S', ∀ y : G, ψ (s * y) = ψ y) →
    (∀ x : G, ∑' δ : D, ‖φ ((δ : G) * x)‖ₑ ≠ ⊤) →
    (∀ x : G, ∑' δ' : D', ‖ψ ((δ' : G) * x)‖ₑ ≠ ⊤) →
    (∫⁻ x in FΓ, (∑' δ : D, ‖φ ((δ : G) * x)‖ₑ) * (∑' δ' : D', ‖ψ ((δ' : G) * x)‖ₑ) ∂μ) ≠ ⊤ →
    IntegrableOn (fun x => poinc D φ x * poinc D' ψ x) FΓ μ ∧
    (∫ x in FΓ, poinc D φ x * poinc D' ψ x ∂μ)
      = ∑' r : R, ∫ x in Fs r, φ x * ψ ((r : G)⁻¹ * x) ∂μ

end PI.PoincareSeriesInner.W
