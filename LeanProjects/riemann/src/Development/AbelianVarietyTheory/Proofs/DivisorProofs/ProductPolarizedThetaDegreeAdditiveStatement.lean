import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductPolarizedThetaDegreeAdditive
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_polarized_theta_degree_additive : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsRegSurf p → ∀ P₁ P₂ : PPAS S, P₁.HasTheta → P₂.HasTheta → ∃ P : PPAS S, P.g = P₁.g + P₂.g ∧ P.HasTheta ∧ P.degOmega p = P₁.degOmega p + P₂.degOmega p ∧ ∀ a b : ℝ, P₁.IsCh2Omega p a → P₂.IsCh2Omega p b → P.IsCh2Omega p (a + b) := by
  first | exact @GlobalTheory.PPAS.exists_prod_ch2Omega | exact GlobalTheory.PPAS.exists_prod_ch2Omega | (intros; apply GlobalTheory.PPAS.exists_prod_ch2Omega <;> assumption)
