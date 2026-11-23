import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoverOverIntegersExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_cover_over_integers_exists : GlobalTheory.Published.RegularAlteration → ∀ (K : Type) [Field K] [NumberField K] (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsArithVar p 1 → ∃ C : RegCover p, Nonempty (C.Y ⟶ Sp (𝓞 K)) := by
  first | exact @GlobalTheory.RegCoverToIntegers.exists_regCover_toIntegers | exact GlobalTheory.RegCoverToIntegers.exists_regCover_toIntegers | (intros; apply GlobalTheory.RegCoverToIntegers.exists_regCover_toIntegers <;> assumption)
