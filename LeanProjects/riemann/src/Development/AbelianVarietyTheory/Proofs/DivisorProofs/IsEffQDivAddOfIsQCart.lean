import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem isEffQDiv_add {X : Scheme.{0}} {Δ D : X → ℚ} (hΔ : IsEffQDiv Δ) (hD : IsEffQDiv D) :
    IsEffQDiv (Δ + D) where
  finite := (hΔ.finite.union hD.finite).subset (Function.support_add _ _)
  coheight z hz := by
    by_cases h : Δ z = 0
    · exact hD.coheight z fun h' => hz (by simp [h, h'])
    · exact hΔ.coheight z h
  nonneg z := add_nonneg (hΔ.nonneg z) (hD.nonneg z)

theorem isEffQDiv_add_of_isQCart : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (Δ D : X → ℚ), IsEffQDiv Δ → IsQCart D → IsEffQDiv (Δ + D) := by
  intro X _ _ p hp Δ D hΔ hD
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨m, D₀, -, hD₀, rfl⟩ := hD
  exact isEffQDiv_add hΔ (isEffQDiv_qWeil hD₀ m)

end GlobalTheory.PairStep
