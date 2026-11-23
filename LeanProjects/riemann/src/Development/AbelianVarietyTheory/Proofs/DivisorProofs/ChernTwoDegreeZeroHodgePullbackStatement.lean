import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTwoDegreeZeroHodgePullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPullbackComposite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHodgeCh2Omega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_two_degree_zero_hodge_pullback : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (K : Type) [Field K] [NumberField K] (E : PPAS (Sp (𝓞 K))), E.HasTheta → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) [IsIntegral Y], IsRegSurf p → ∀ (q : Y ⟶ Sp (𝓞 K)) (Q : PPAS Y) (φ : Q.A.left ⟶ E.A.left), Q.IsPull E q φ → ∀ h : VMetric p (LieVB.omega Q.A) Q.g, Q.IsHodge h → h.IsCInfNorm → ∀ a : ℝ, h.IsCh2Deg a → a = 0 := by
  first | exact @GlobalTheory.FlagValuationRings.ch2Deg_eq_zero | exact GlobalTheory.FlagValuationRings.ch2Deg_eq_zero | (intros; apply GlobalTheory.FlagValuationRings.ch2Deg_eq_zero <;> assumption)
