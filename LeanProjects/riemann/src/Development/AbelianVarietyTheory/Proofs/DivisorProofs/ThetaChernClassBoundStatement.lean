import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaChernClassBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_chern_class_bound : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ArithRiemannRoch → ∀ g : ℕ, ∃ r : ℝ, ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsRegSurf p → ∀ P : PPAS S, P.g = g → P.HasTheta → P.IsCh2Omega p (r / 2 * (P.degOmega p : ℝ)) := by
  first | exact @GlobalTheory.ThetaRR.exists_const_ch2Omega | exact GlobalTheory.ThetaRR.exists_const_ch2Omega | (intros; apply GlobalTheory.ThetaRR.exists_const_ch2Omega <;> assumption)
