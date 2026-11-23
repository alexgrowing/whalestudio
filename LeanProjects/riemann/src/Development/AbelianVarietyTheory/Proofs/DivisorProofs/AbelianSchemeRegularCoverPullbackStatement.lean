import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeRegularCoverPullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_regular_cover_pullback : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∀ P : PPAS X, ∃ (C : RegCover p) (P' : PPAS C.Y) (φ : P'.A.left ⟶ P.A.left), P'.IsPull P C.ρ φ ∧ P'.g = P.g ∧ P'.HasTheta := by
  first | exact @GlobalTheory.ThetaCover.exists_regCover_hasTheta | exact GlobalTheory.ThetaCover.exists_regCover_hasTheta | (intros; apply GlobalTheory.ThetaCover.exists_regCover_hasTheta <;> assumption)
