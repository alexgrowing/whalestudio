import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

def ResidueGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
    mIdealOver F y ≤ mIdealOver F y' →
    ∀ (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
      (∀ (f g : MRingOver F ι) (n : K → ℕ), IsMultiHomog f n → IsMultiHomog g n → aeval y' g ≠ 0 →
        ∃ h : aeval y f / aeval y g ∈ R, σ ⟨_, h⟩ = aeval y' f / aeval y' g) →
      (∀ d : ∀ k, ι k, (∀ k, y' ⟨k, d k⟩ ≠ 0) → ∀ z ∈ chartRingOver F y d,
        ∃ h : z ∈ R, σ ⟨z, h⟩ ∈ chartRingOver F y' d) →
    ∀ β : K → ℤ, IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y β → ∀ d₀ : ∀ k, ι k, (∀ k, y' ⟨k, d₀ k⟩ ≠ 0) →
      ∃ ρ : Ω → K',
        (∀ h ∈ secOver F y β, ∃ hh : h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k) ∈ R,
          σ ⟨_, hh⟩ = ρ h * ∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) ∧
        ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
          Submodule.span (chartRingOver F y' c) (ρ '' (secOver F y β : Set Ω)) =
            Submodule.span (chartRingOver F y' c) {(∏ k, y' ⟨k, c k⟩ ^ (-β k))⁻¹}

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
