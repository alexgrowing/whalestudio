import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoverPullbackThetaDegree
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_cover_pullback_theta_degree : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsRegSurf p → ∀ (C : RegCover p) (P : PPAS S), P.HasTheta → ∃ P' : PPAS C.Y, P'.g = P.g ∧ P'.HasTheta ∧ P'.degOmega (C.ρ ≫ p) = C.deg * P.degOmega p ∧ ∀ a : ℝ, P.IsCh2Omega p a → P'.IsCh2Omega (C.ρ ≫ p) (C.deg * a) := by
  first | exact @GlobalTheory.PPAS.exists_pull_regCover_ch2Omega | exact GlobalTheory.PPAS.exists_pull_regCover_ch2Omega | (intros; apply GlobalTheory.PPAS.exists_pull_regCover_ch2Omega <;> assumption)
