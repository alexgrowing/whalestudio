import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldCoordsGenerated
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fraction_field_coords_generated : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω),
    CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ a : Ω, ∃ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ t ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), t ≠ 0 ∧ a = s / t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart | exact GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart <;> assumption)
