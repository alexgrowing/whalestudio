import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantAbelianSchemeThetaDegreeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_abelian_scheme_theta_degree_zero : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (K : Type) [Field K] [NumberField K] (E : PPAS (Sp (𝓞 K))), E.HasTheta → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) [IsIntegral Y], IsRegSurf p → ∀ q : Y ⟶ Sp (𝓞 K), ∃ Q : PPAS Y, Q.g = E.g ∧ Q.HasTheta ∧ Q.degOmega p = 0 ∧ Q.IsCh2Omega p 0 := by
  first | exact @GlobalTheory.PPAS.exists_pull_ringOfIntegers_ch2Omega_zero | exact GlobalTheory.PPAS.exists_pull_ringOfIntegers_ch2Omega_zero | (intros; apply GlobalTheory.PPAS.exists_pull_ringOfIntegers_ch2Omega_zero <;> assumption)
