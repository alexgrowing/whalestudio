import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartLieBasisMatrices

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory

theorem exists_open_isDomain_of_smooth_complex :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ x : Y,
      ∃ U : Y.Opens, x ∈ U ∧ ∀ V : Y.Opens, V ≤ U → x ∈ V → IsDomain Γ(Y, V) := by
  intro Y p D hp x
  have hs : Smooth p := SmoothOfRelativeDimension.smooth D p
  obtain ⟨-, hn, hl⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Y p hs
  have := IsNormalScheme.of_pred hn
  obtain ⟨U, hx, hU⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y x
  exact ⟨U, hx, fun V hV hxV => hU V hxV hV⟩

end GlobalTheory
